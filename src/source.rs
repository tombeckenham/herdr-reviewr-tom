//! The read-only Source provider behind `src/forge.rs`, through `src api`.

use std::path::Path;
use std::sync::atomic::AtomicBool;

use serde_json::Value;

use crate::forge::{
    AssocPr, Association, Check, CheckStatus, Comment, CommentKind, FindingPlace, Merge,
    PrFetchInput, PrSnapshot, PrState, PrView, Reply, Sync, finding_side, finish_comments,
    prose_row, push_unique, upsert_latest,
};

/// Read Source for one already-derived input. Degradation stays in-band for the PR tab.
pub(crate) fn fetch(
    repo: &Path,
    input: &PrFetchInput,
    target: &crate::git::RepoTarget,
    cancelled: &AtomicBool,
) -> PrView {
    match fetch_inner(repo, input, target, cancelled) {
        Ok(view) => view,
        Err(error) => error.into_view(target.host()),
    }
}

/// A classified `src` failure, mapped to a [`PrView`] degraded state.
#[derive(Debug)]
enum SrcError {
    NoSrc,
    NotAuthed,
    /// A 404: the pull request or repository is gone, or the caller may not see it.
    Unavailable(String),
    /// A 403. Checks and line threads treat it as empty; the pull request itself does not.
    Denied(String),
    LocalGit(String),
    Other(String),
}

impl SrcError {
    fn into_view(self, host: &str) -> PrView {
        match self {
            Self::NoSrc => PrView::NoCli(crate::git::Forge::Source),
            Self::NotAuthed => PrView::NotAuthed(crate::git::Forge::Source, host.to_owned()),
            Self::LocalGit(message) => PrView::GitError(message),
            Self::Unavailable(message) | Self::Denied(message) | Self::Other(message) => {
                PrView::Error(crate::git::Forge::Source, message)
            }
        }
    }
}

/// The retryable error a panicked reader degrades into (`crate::forge::join_read`).
fn died(surface: &str) -> SrcError {
    SrcError::Other(format!("{surface} read panicked"))
}

/// A JSON array as a slice, empty when the value is not one.
fn array(value: &Value) -> &[Value] {
    value.as_array().map_or(&[], Vec::as_slice)
}

/// An unreadable optional surface reads as empty instead of failing the fetch.
fn optional_surface(result: Result<Value, SrcError>) -> Result<Value, SrcError> {
    match result {
        Err(SrcError::Unavailable(_) | SrcError::Denied(_)) => Ok(Value::Null),
        other => other,
    }
}

/// Run one `src api` read against `host` and parse the JSON body.
fn src_api(
    repo: &Path,
    host: &str,
    endpoint: &str,
    cancelled: &AtomicBool,
) -> Result<Value, SrcError> {
    let mut cmd = crate::proc::command("src");
    cmd.current_dir(repo).args(["api", "--hostname", host, endpoint]);
    let out = crate::forge::run_provider(
        cmd,
        cancelled,
        SrcError::NoSrc,
        classify_failure,
        SrcError::Other,
    )?;
    serde_json::from_str(out.trim()).map_err(|error| SrcError::Other(error.to_string()))
}

/// A failed `src`'s state by stderr wording. `src` prints `(HTTP nnn)` and exits 1.
fn classify_failure(stderr: &str) -> SrcError {
    let s = stderr.to_lowercase();
    if s.contains("not logged")
        || s.contains("src auth login")
        || crate::forge::reports_status(&s, 401)
    {
        SrcError::NotAuthed
    } else if crate::forge::reports_status(&s, 404) {
        SrcError::Unavailable(stderr.trim().to_string())
    } else if crate::forge::reports_status(&s, 403) {
        SrcError::Denied(stderr.trim().to_string())
    } else {
        SrcError::Other(stderr.trim().to_string())
    }
}

fn fetch_inner(
    repo: &Path,
    input: &PrFetchInput,
    target: &crate::git::RepoTarget,
    cancelled: &AtomicBool,
) -> Result<PrView, SrcError> {
    // A fork pull request's head is `refs/pull/N/head`, which no head-name list finds: read the pin.
    let pinned = match input.local.pin_on(crate::git::Forge::Source) {
        Some(pin) => read_pull(repo, &pin.repo, pin.number, cancelled)?
            .map(|pull| (pin.number, pull, &pin.repo)),
        None => None,
    };
    let (number, listed, project) = if let Some(pinned) = pinned {
        pinned
    } else {
        let Some((picked, project)) = associate(repo, input, target, cancelled)? else {
            return Ok(PrView::NoPr);
        };
        (picked.number, picked.raw.unwrap_or(Value::Null), project)
    };
    let host = project.host();
    // The pull route compares the whole diff. The list, one issue page, and the stored head do not.
    let read_checks = |sha: &str| {
        optional_surface(src_api(
            repo,
            host,
            &format!("{}/check-runs?sha={sha}", repo_path(project)),
            cancelled,
        ))
    };
    // The gate names the head a round late, so guess the local one: an in-sync branch saves a round.
    let guess = input.local.head_oid.as_deref().filter(|oid| oid.len() == 40);
    let (issue, threads, gate, guessed) = std::thread::scope(|scope| {
        let guessed = guess.map(|sha| scope.spawn(move || read_checks(sha)));
        let issue = scope.spawn(|| read_issue(repo, host, project, number, cancelled));
        let threads = scope.spawn(|| {
            optional_surface(src_api(
                repo,
                host,
                &format!("{}/pulls/{number}/comments", repo_path(project)),
                cancelled,
            ))
        });
        let gate = scope.spawn(|| read_gate(repo, host, project, number, cancelled));
        (
            crate::forge::join_read(issue, || died("issue")),
            crate::forge::join_read(threads, || died("threads")),
            crate::forge::join_read(gate, || died("head")),
            guessed.map(|guessed| crate::forge::join_read(guessed, || died("checks"))),
        )
    });
    let (issue, truncated) = issue?;
    let Some(gate) = gate? else { return Ok(PrView::NoPr) };
    let pr_head = gate["headSha"].as_str().unwrap_or_default();
    let sync = crate::forge::local_sync(repo, input.local.head_oid.as_deref(), pr_head)
        .map_err(|error| SrcError::LocalGit(error.0))?;
    let checks = match guessed {
        Some(guessed) if guess == Some(pr_head) => guessed?,
        _ if pr_head.len() == 40 => read_checks(pr_head)?,
        _ => Value::Array(Vec::new()),
    };
    Ok(PrView::Pr(Box::new(build_snapshot(
        project,
        &PullRead { listed: &listed, issue: &issue, gate: &gate },
        sync,
        &threads?,
        &checks,
        truncated,
    ))))
}

/// `repos/{owner}/{repo}` under `/api/v1`, both segments encoded.
fn repo_path(project: &crate::git::RepoTarget) -> String {
    format!(
        "repos/{}/{}",
        crate::forge::urlencode(project.owner()),
        crate::forge::urlencode(project.name())
    )
}

/// One pull request, standing in for its list row. `None` when a stale pin names none.
fn read_pull(
    repo: &Path,
    project: &crate::git::RepoTarget,
    number: u64,
    cancelled: &AtomicBool,
) -> Result<Option<Value>, SrcError> {
    let endpoint = format!("{}/pulls/{number}", repo_path(project));
    match src_api(repo, project.host(), &endpoint, cancelled) {
        Ok(pull) => Ok(Some(pull)),
        Err(SrcError::Unavailable(_)) => Ok(None),
        Err(error) => Err(error),
    }
}

/// The issue page: body, url, and the first timeline page. A hidden issue leaves the list row to stand.
fn read_issue(
    repo: &Path,
    host: &str,
    project: &crate::git::RepoTarget,
    number: u64,
    cancelled: &AtomicBool,
) -> Result<(Value, bool), SrcError> {
    let page =
        match src_api(repo, host, &format!("{}/issues/{number}", repo_path(project)), cancelled) {
            Ok(page) => page,
            Err(SrcError::Unavailable(_) | SrcError::Denied(_)) => return Ok((Value::Null, false)),
            Err(error) => return Err(error),
        };
    // Oldest first, 100 at a time. Stopping here keeps that page and marks the rest truncated.
    let truncated = page["next"].as_str().is_some_and(|next| !next.is_empty());
    Ok((page, truncated))
}

/// The list row, the issue page, and the stored head one snapshot is built from.
#[derive(Copy, Clone)]
struct PullRead<'a> {
    listed: &'a Value,
    issue: &'a Value,
    gate: &'a Value,
}

/// Stored head and base. `None` when the pull request is gone. This route does not compare.
fn read_gate(
    repo: &Path,
    host: &str,
    project: &crate::git::RepoTarget,
    number: u64,
    cancelled: &AtomicBool,
) -> Result<Option<Value>, SrcError> {
    match src_api(repo, host, &format!("{}/pulls/{number}/checks", repo_path(project)), cancelled) {
        Ok(gate) => Ok(Some(gate)),
        Err(SrcError::Unavailable(_)) => Ok(None),
        Err(SrcError::Denied(_)) => Ok(Some(Value::Null)),
        Err(error) => Err(error),
    }
}

/// The branch's pull request. Upstream wins over the fork clone's `origin`.
fn associate<'a>(
    repo: &Path,
    input: &'a PrFetchInput,
    target: &'a crate::git::RepoTarget,
    cancelled: &AtomicBool,
) -> Result<Option<(AssocPr, &'a crate::git::RepoTarget)>, SrcError> {
    let names = input.local.head_names();
    if names.is_empty() {
        return Ok(None);
    }
    let head = input.local.head_oid.as_deref();
    let fork = crate::forge::fork_repository(input.origin_repository.as_ref(), target);
    let mut projects = vec![target];
    if let Some(fork) = fork {
        projects.push(fork);
    }
    for project in projects {
        if let Some(pr) = pick_project(repo, project, &names, &input.local.heads, head, cancelled)?
        {
            return Ok(Some((pr, project)));
        }
    }
    Ok(None)
}

/// This project's open pull request, else its finished one. Closed lists wait until open is empty.
fn pick_project(
    repo: &Path,
    project: &crate::git::RepoTarget,
    names: &[String],
    heads: &[crate::git::Head],
    head: Option<&str>,
    cancelled: &AtomicBool,
) -> Result<Option<AssocPr>, SrcError> {
    let mut assoc = admitted(&list_state(repo, project, names, "open", cancelled)?, project, heads);
    if !assoc.open.is_empty()
        && let Some(number) = resolve(repo, &assoc, head)?
    {
        return Ok(take_numbered(&mut assoc, number));
    }
    let closed = admitted(&list_state(repo, project, names, "closed", cancelled)?, project, heads);
    assoc.history = closed.history;
    if assoc.open.is_empty() {
        hydrate_history(repo, project, &mut assoc.history, cancelled)?;
    }
    let Some(number) = resolve(repo, &assoc, head)? else { return Ok(None) };
    Ok(take_numbered(&mut assoc, number))
}

fn resolve(repo: &Path, assoc: &Association, head: Option<&str>) -> Result<Option<u64>, SrcError> {
    crate::forge::resolve_pick(repo, assoc, head).map_err(|error| SrcError::LocalGit(error.0))
}

fn take_numbered(assoc: &mut Association, number: u64) -> Option<AssocPr> {
    if let Some(index) = assoc.open.iter().position(|pr| pr.number == number) {
        return Some(assoc.open.swap_remove(index));
    }
    let index = assoc.history.iter().position(|pr| pr.number == number)?;
    Some(assoc.history.swap_remove(index))
}

/// One list page per head name. A missing repository is an empty page.
fn list_state(
    repo: &Path,
    project: &crate::git::RepoTarget,
    names: &[String],
    state: &str,
    cancelled: &AtomicBool,
) -> Result<Vec<Value>, SrcError> {
    let jobs: Vec<(&crate::git::RepoTarget, String)> = names
        .iter()
        .map(|name| {
            let endpoint = format!(
                "{}/pulls?state={state}&head={}",
                repo_path(project),
                crate::forge::urlencode(name)
            );
            (project, endpoint)
        })
        .collect();
    let mut pages = Vec::new();
    for response in src_fan_out(repo, project.host(), &jobs, cancelled) {
        match response {
            Err(SrcError::Unavailable(_)) => {}
            other => pages.push(other?),
        }
    }
    Ok(pages)
}

/// Admitted rows from list pages, open and finished kept apart.
fn admitted(
    pages: &[Value],
    project: &crate::git::RepoTarget,
    heads: &[crate::git::Head],
) -> Association {
    let mut assoc = Association::default();
    for page in pages {
        for item in page["items"].as_array().into_iter().flatten() {
            let Some(pr) = admit(item, project, heads) else { continue };
            match item["state"].as_str() {
                Some("open") => push_unique(&mut assoc.open, pr),
                Some("merged" | "closed") => push_unique(&mut assoc.history, pr),
                _ => {}
            }
        }
    }
    assoc
}

/// List calls for one fetch, results in call order.
fn src_fan_out(
    repo: &Path,
    host: &str,
    jobs: &[(&crate::git::RepoTarget, String)],
    cancelled: &AtomicBool,
) -> Vec<Result<Value, SrcError>> {
    std::thread::scope(|scope| {
        let handles: Vec<_> = jobs
            .iter()
            .map(|(_, endpoint)| {
                let endpoint = endpoint.clone();
                scope.spawn(move || src_api(repo, host, &endpoint, cancelled))
            })
            .collect();
        handles.into_iter().map(|handle| crate::forge::join_read(handle, || died("list"))).collect()
    })
}

/// How many closed candidates get a head commit before the ancestry guard. Matches `resolve_pick`.
const HISTORY_OID_CAP: usize = 10;

/// Fill `head_oid` on the newest history rows. The list has no commit and no close time.
fn hydrate_history(
    repo: &Path,
    project: &crate::git::RepoTarget,
    history: &mut Vec<AssocPr>,
    cancelled: &AtomicBool,
) -> Result<(), SrcError> {
    history.sort_by(|a, b| b.created_at.cmp(&a.created_at));
    history.truncate(HISTORY_OID_CAP);
    let host = project.host();
    let shas = std::thread::scope(|scope| {
        let handles: Vec<_> = history
            .iter()
            .map(|pr| scope.spawn(|| read_gate(repo, host, project, pr.number, cancelled)))
            .collect();
        handles
            .into_iter()
            .map(|handle| crate::forge::join_read(handle, || died("head")))
            .collect::<Vec<_>>()
    });
    for (pr, gate) in history.iter_mut().zip(shas) {
        pr.head_oid =
            gate?.and_then(|gate| gate["headSha"].as_str().map(str::to_string)).unwrap_or_default();
    }
    history.retain(|pr| !pr.head_oid.is_empty());
    Ok(())
}

/// One list row the branch's published heads admit. `None` for a hidden or foreign head.
fn admit(
    item: &Value,
    queried: &crate::git::RepoTarget,
    heads: &[crate::git::Head],
) -> Option<AssocPr> {
    let head = item["head"].as_str().unwrap_or("");
    let (owner, branch) = match head.split_once(':') {
        Some((owner, branch)) if !owner.is_empty() && !branch.is_empty() => (Some(owner), branch),
        _ if !head.is_empty() => (None, head),
        _ => return None,
    };
    let fork = owner.and_then(|owner| {
        crate::git::RepoTarget::with_path(
            crate::git::Forge::Source,
            queried.host(),
            &[owner, queried.name()],
        )
    });
    let head_repo = if owner.is_some() {
        crate::forge::HeadRepo::Other(fork.iter().collect())
    } else {
        crate::forge::HeadRepo::Queried
    };
    if !crate::forge::admits(heads, queried, branch, &head_repo) {
        return None;
    }
    let number = item["number"].as_u64()?;
    let created_at = rfc3339_ms(item["createdAt"].as_u64().unwrap_or(0));
    Some(AssocPr {
        number,
        head_oid: String::new(),
        head_ref: branch.to_string(),
        created_at: created_at.clone(),
        // The list has no close time, so history sorts by when the pull request opened.
        closed_at: created_at,
        raw: Some(item.clone()),
    })
}

/// Assemble the snapshot from the list row, the issue page, the stored head, threads, and checks.
fn build_snapshot(
    project: &crate::git::RepoTarget,
    read: &PullRead<'_>,
    sync: Sync,
    threads: &Value,
    checks: &Value,
    timeline_truncated: bool,
) -> PrSnapshot {
    let PullRead { listed, issue, gate } = *read;
    let head = listed["head"].as_str().unwrap_or("");
    let (owner, branch) = match head.split_once(':') {
        Some((owner, branch)) if !owner.is_empty() && !branch.is_empty() => (Some(owner), branch),
        _ => (None, head),
    };
    let head_repo = listed["headRepo"].as_str().unwrap_or("");
    let same_repo = head_repo.is_empty()
        || (head_repo.eq_ignore_ascii_case(&format!("{}/{}", project.owner(), project.name())));
    let thread_rows = array(threads);
    let threads_truncated = thread_rows.len() > crate::forge::SURFACE_CAP;
    let timeline = array(&issue["timeline"]);
    let mut comments = prose_comments(timeline);
    comments.extend(finding_comments(thread_rows));
    let comments_truncated =
        timeline_truncated || threads_truncated || comments.len() > crate::forge::SURFACE_CAP;
    finish_comments(&mut comments);
    if comments.len() > crate::forge::SURFACE_CAP {
        comments.truncate(crate::forge::SURFACE_CAP);
    }
    PrSnapshot {
        number: listed["number"].as_u64().unwrap_or_default(),
        title: listed["title"].as_str().unwrap_or_default().to_string(),
        url: issue["htmlUrl"].as_str().unwrap_or_default().to_string(),
        body: issue["body"].as_str().unwrap_or_default().to_string(),
        state: parse_state(listed["state"].as_str().unwrap_or("open")),
        is_draft: listed["draft"].as_bool().unwrap_or(false),
        head_ref: branch.to_string(),
        head_is_fork: owner.is_some() || !same_repo,
        head_oid: gate["headSha"].as_str().unwrap_or_default().to_string(),
        base_ref: gate["base"].as_str().unwrap_or_default().to_string(),
        // The list row says `conflicts`; a pinned read is the pull itself, which says `mergeable`.
        merge: if listed["buckets"]["conflicts"].as_bool() == Some(true)
            || (listed["state"] == "open" && listed["mergeable"].as_bool() == Some(false))
        {
            Merge::Conflicting
        } else {
            Merge::Clean
        },
        sync,
        checks: normalize_checks(checks),
        comments,
        comments_truncated,
        checks_truncated: false,
    }
}

fn parse_state(state: &str) -> PrState {
    match state {
        "merged" => PrState::Merged,
        "closed" => PrState::Closed,
        _ => PrState::Open,
    }
}

/// Reviews and conversation comments. A line comment carries `path` and is a finding instead.
fn prose_comments(timeline: &[Value]) -> Vec<Comment> {
    let mut out = Vec::new();
    for row in timeline {
        if row.get("path").is_some() {
            continue;
        }
        let body = row["comment"].as_str().unwrap_or("").trim().to_string();
        if body.is_empty() {
            continue;
        }
        let (author, bot) = author_of(row);
        let kind =
            if row["review"].is_string() { CommentKind::Review } else { CommentKind::Comment };
        out.push(prose_row(kind, author, bot, body, stamp(row)));
    }
    out
}

/// Line-comment threads, oldest first as the forge lists them. The newest 100 survive the cap.
fn finding_comments(threads: &[Value]) -> Vec<Comment> {
    let mut out = Vec::new();
    for thread in threads {
        let nodes = array(&thread["comments"]);
        let Some(root_i) = nodes
            .iter()
            .position(|node| node["comment"].as_str().is_some_and(|body| !body.trim().is_empty()))
        else {
            continue;
        };
        let root = &nodes[root_i];
        let (author, bot) = author_of(root);
        let path = thread["path"].as_str().unwrap_or("");
        let side = thread["side"].as_str();
        let place = FindingPlace::from_lines(
            path,
            thread["startLine"].as_u64(),
            thread["line"].as_u64(),
            finding_side(side == Some("new"), side == Some("old")),
        );
        let snippet =
            thread["diffHunk"].as_str().filter(|hunk| !hunk.is_empty()).map(str::to_string);
        out.push(Comment {
            kind: CommentKind::Finding,
            author,
            author_is_bot: bot,
            anchor: place.anchor(),
            place: Some(place),
            body: root["comment"].as_str().unwrap_or("").trim().to_string(),
            snippet,
            created_at: stamp(root),
            is_resolved: thread["resolved"].as_bool().unwrap_or(false),
            is_outdated: thread["outdated"].as_bool().unwrap_or(false),
            replies: replies_after(&nodes[root_i..]),
        });
    }
    crate::forge::newest_capped(out)
}

fn replies_after(nodes: &[Value]) -> Vec<Reply> {
    nodes
        .iter()
        .skip(1)
        .filter_map(|node| {
            let body = node["comment"].as_str().unwrap_or("").trim();
            if body.is_empty() {
                return None;
            }
            let (author, bot) = author_of(node);
            Some(Reply {
                author,
                author_is_bot: bot,
                body: body.to_string(),
                created_at: stamp(node),
            })
        })
        .collect()
}

/// The login, and whether an agent wrote the comment.
fn author_of(row: &Value) -> (String, bool) {
    let author = row["author"].as_str().unwrap_or("").to_string();
    let agent = row["agent"].as_str().filter(|agent| !agent.is_empty());
    let bot = agent.is_some() || crate::forge::is_named_bot(&author);
    let name = if author.is_empty() { agent.unwrap_or("").to_string() } else { author };
    (name, bot)
}

/// `at` or `createdAt` milliseconds as RFC 3339, so the newest-first sort and age labels agree.
fn stamp(row: &Value) -> String {
    let ms = row["at"].as_u64().or_else(|| row["createdAt"].as_u64()).unwrap_or(0);
    if ms == 0 { String::new() } else { rfc3339_ms(ms) }
}

/// Unix milliseconds as `YYYY-MM-DDTHH:MM:SS.mmmZ`. Fixed width, so the strings sort in time order.
fn rfc3339_ms(ms: u64) -> String {
    let seconds = (ms / 1000) as i64;
    let millis = ms % 1000;
    let Ok(time) = time::OffsetDateTime::from_unix_timestamp(seconds) else {
        return String::new();
    };
    format!(
        "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}.{millis:03}Z",
        time.year(),
        u8::from(time.month()),
        time.day(),
        time.hour(),
        time.minute(),
        time.second()
    )
}

/// The latest run of each check name. A `superseded` re-run is the earlier one.
fn normalize_checks(checks: &Value) -> Vec<Check> {
    let mut out = Vec::new();
    for run in checks.as_array().into_iter().flatten() {
        if run["superseded"].as_bool() == Some(true) {
            continue;
        }
        let name = run["name"].as_str().unwrap_or("").to_string();
        if name.is_empty() {
            continue;
        }
        upsert_latest(&mut out, Check { name, status: check_status(run) });
    }
    out
}

/// Source's `status`/`conclusion`, in the buckets `src pr checks` uses.
fn check_status(run: &Value) -> CheckStatus {
    let status = run["status"].as_str().unwrap_or("");
    let conclusion = run["conclusion"].as_str().unwrap_or("");
    let state = if status == "completed" { conclusion } else { status };
    match state.to_ascii_lowercase().as_str() {
        "success" => CheckStatus::Success,
        "skipped" | "neutral" => CheckStatus::Skipped,
        "in_progress" => CheckStatus::Running,
        "queued" | "pending" | "" => CheckStatus::Pending,
        _ => CheckStatus::Failure,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn project() -> crate::git::RepoTarget {
        crate::git::RepoTarget::with_path(
            crate::git::Forge::Source,
            "source.tanstack.com",
            &["TanStack", "source"],
        )
        .unwrap()
    }

    fn head(name: &str) -> crate::git::Head {
        crate::git::Head { repo: project(), name: name.to_string() }
    }

    #[test]
    fn a_same_repo_head_is_admitted_and_a_stranger_fork_is_not() {
        let heads = [head("feature")];
        let item = serde_json::json!({"number": 7, "state": "open", "head": "feature", "createdAt": 1_700_000_000_000_u64});
        let pr = admit(&item, &project(), &heads).unwrap();
        assert_eq!(pr.number, 7);
        assert_eq!(pr.head_ref, "feature");
        assert_eq!(pr.created_at, "2023-11-14T22:13:20.000Z");
        let fork = serde_json::json!({"number": 8, "head": "someone:feature", "createdAt": 1});
        assert!(admit(&fork, &project(), &heads).is_none());
        let fork_head = crate::git::Head {
            repo: crate::git::RepoTarget::with_path(
                crate::git::Forge::Source,
                "source.tanstack.com",
                &["someone", "source"],
            )
            .unwrap(),
            name: "feature".to_string(),
        };
        assert_eq!(admit(&fork, &project(), &[fork_head]).unwrap().number, 8);
    }

    #[test]
    fn the_snapshot_keeps_a_review_a_finding_and_a_failing_check() {
        let listed = serde_json::json!({
            "number": 12,
            "title": "Add source",
            "state": "open",
            "draft": false,
            "head": "feature",
            "buckets": {"conflicts": true}
        });
        let gate = serde_json::json!({"base": "main", "headSha": "abc"});
        let issue = serde_json::json!({
            "htmlUrl": "https://source.tanstack.com/@TanStack/source/pull/12",
            "body": "The body",
            "timeline": [{
                "comment": "Looks good",
                "author": "ada",
                "review": "approved",
                "at": 1_700_000_000_000_u64
            }]
        });
        let threads = serde_json::json!([{
            "path": "src/a.rs",
            "side": "new",
            "line": 4,
            "startLine": null,
            "diffHunk": "@@ -1 +1 @@",
            "outdated": false,
            "resolved": true,
            "comments": [{"comment": "Here", "author": "grace", "at": 1_700_000_000_100_u64}]
        }]);
        let checks = serde_json::json!([
            {"name": "ci", "status": "completed", "conclusion": "failure"},
            {"name": "ci", "status": "completed", "conclusion": "success", "superseded": true}
        ]);
        let snapshot = build_snapshot(
            &project(),
            &PullRead { listed: &listed, issue: &issue, gate: &gate },
            Sync::InSync,
            &threads,
            &checks,
            false,
        );
        assert_eq!(snapshot.number, 12);
        assert_eq!(snapshot.title, "Add source");
        assert_eq!(snapshot.body, "The body");
        assert_eq!(snapshot.head_oid, "abc");
        assert_eq!(snapshot.base_ref, "main");
        assert_eq!(snapshot.state, PrState::Open);
        assert_eq!(snapshot.merge, Merge::Conflicting);
        assert!(!snapshot.head_is_fork);
        assert_eq!(
            snapshot.checks,
            vec![Check { name: "ci".into(), status: CheckStatus::Failure }]
        );
        assert!(snapshot.comments.iter().any(|comment| comment.kind == CommentKind::Review));
        let finding =
            snapshot.comments.iter().find(|comment| comment.kind == CommentKind::Finding).unwrap();
        assert_eq!(finding.anchor, "src/a.rs:4");
        assert!(finding.is_resolved);
        assert_eq!(finding.snippet.as_deref(), Some("@@ -1 +1 @@"));
    }

    #[test]
    fn auth_and_a_missing_pull_request_classify_apart_from_other_failures() {
        assert!(matches!(
            classify_failure(
                "src: The forge did not accept your login (HTTP 401). Run src auth login."
            ),
            SrcError::NotAuthed
        ));
        assert!(matches!(
            classify_failure("src: Pull request not found (HTTP 404). Check the owner."),
            SrcError::Unavailable(_)
        ));
        assert!(matches!(classify_failure("src: HTTP 500"), SrcError::Other(_)));
        assert!(matches!(
            classify_failure("src: jobs:read is required (HTTP 403)."),
            SrcError::Denied(_)
        ));
    }
}
