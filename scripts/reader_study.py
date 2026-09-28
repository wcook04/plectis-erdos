#!/usr/bin/env python3
"""Offline, provider-neutral study preparation, blinding and paired analysis.
Proposed public owner: scripts/benchmark_semantic_reasoning.py (new subcommands).
Reuse scripts/build_benchmark_packet.py for historical cuts after restoring its
source-bound dependencies. This adapter NEVER provisions an execution sandbox,
launches an LLM, decides mathematical correctness, or declares preregistration.
Python standard library only. All outputs are written outside the source tree.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import random
import re
import shutil
from statistics import mean
from typing import Any

ARMS = ('P', 'R', 'F', 'A')
ANALYSIS_PLAN = {
    'primary': {'baseline': 'P', 'treatment': 'F'},
    'minimum_useful_difference': .10,
    'primary_test': 'two_sided_exact_mcnemar',
    'secondary_policy': 'descriptive_without_preregistered_multiplicity_plan',
}
# Known answer-bearing files in the attached benchmark material, not an exhaustive
# semantic leak detector. A human must review transitive projections and aliases.
DENY_NAMES = {'gold.json', 'gold.jsonl', 'grades.jsonl', 'answer_key.json',
              'benchmark_items.json', 'benchmark_results.json', 'theory_lab.json'}


def canonical(obj: Any) -> bytes:
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load(path: Path) -> Any:
    return json.loads(path.read_text(encoding='utf-8'))


def write(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def safe_file(root: Path, relative: str) -> Path:
    """Read an explicit allowlist; reject traversal and symlinked ancestors."""
    rel = PurePosixPath(relative)
    if not relative or rel.is_absolute() or '..' in rel.parts or '\\' in relative:
        raise ValueError(f'unsafe source path: {relative!r}')
    if any(p in ('.git', 'gold', 'private_grading', 'answers') for p in rel.parts) or rel.name in DENY_NAMES:
        raise ValueError(f'known answer/history path is not agent material: {relative}')
    root = root.resolve(strict=True)
    current = root
    for component in rel.parts:
        current = current / component
        if current.is_symlink():
            raise ValueError(f'symlink in source path: {relative}')
    current.resolve(strict=True).relative_to(root)
    if not current.is_file():
        raise ValueError(f'source is not a regular file: {relative}')
    return current


def prepare(spec: dict, source_root: Path, destination: Path) -> dict:
    """Materialize pre-reviewed task/arm allowlists; control file stays private.

    The source_root is an immutable staging area. Paths can designate native
    compiler output or the same source excerpts flattened for the A ablation.
    A manifest digest proves byte identity, not semantic absence of an answer.
    Runtime isolation must be enforced by the separate Type A execution owner.
    """
    root = source_root.resolve(strict=True)
    destination = destination.absolute()
    if destination.exists():
        raise ValueError('destination already exists; never overwrite a sealed study')
    try:
        destination.resolve().relative_to(root)
        raise ValueError('study output must be outside the source tree')
    except ValueError as e:
        if str(e) == 'study output must be outside the source tree':
            raise
    if spec.get('schema') != 'plectis-reader-study/1':
        raise ValueError('unsupported study schema')
    if type(spec.get('seed')) is not int or not isinstance(spec.get('model_snapshot'), str) or not spec['model_snapshot'].strip():
        raise ValueError('seed and model snapshot required')
    budget = spec.get('budget')
    if not isinstance(budget, dict) or not budget or any(
            type(v) is not int or v <= 0 for v in budget.values()):
        raise ValueError('positive integer resource limits required')
    mode = spec.get('mode')
    if mode not in ('development', 'confirmatory'):
        raise ValueError('mode must be development or confirmatory')
    if spec.get('analysis_plan') not in (None, ANALYSIS_PLAN):
        raise ValueError('analysis plan differs from the fixed F-P primary contract')
    if mode == 'confirmatory' and spec.get('analysis_plan') != ANALYSIS_PLAN:
        raise ValueError('confirmatory study requires an explicit fixed F-P analysis plan')
    tasks = spec.get('tasks', [])
    if not tasks:
        raise ValueError('no reviewed tasks; refuse a pretend experiment')
    ids = set(); families = set(); validated = []
    arms = tuple(spec.get('arms', ARMS))
    if len(set(arms)) != len(arms) or not set(arms) <= set(ARMS) or not arms:
        raise ValueError('invalid arms')
    if mode == 'confirmatory' and not {'P', 'F'} <= set(arms):
        raise ValueError('confirmatory primary analysis requires both P and F arms')
    for task in tasks:
        tid = task.get('task_id'); family = task.get('family_id')
        if not isinstance(tid, str) or not re.fullmatch('[A-Za-z0-9_-]+', tid) or tid in ids:
            raise ValueError('task IDs must be safe and unique')
        if not family or family in families:
            raise ValueError('one independent task family per paired item is required')
        ids.add(tid); families.add(family)
        if mode == 'confirmatory' and task.get('split') != 'sealed_confirmatory':
            raise ValueError('development or pilot task in confirmatory plan')
        if not re.fullmatch('[a-f0-9]{64}', task.get('gold_sha256', '')):
            raise ValueError('task lacks frozen gold digest')
        if not task.get('prompt') or task.get('kind') not in ('frontier', 'restatement', 'status', 'transfer'):
            raise ValueError('invalid task')
        for arm in arms:
            selected = task.get('material', {}).get(arm, [])
            if not selected:
                raise ValueError(f'{tid}/{arm} has no explicit material')
            selected_paths = set()
            for ref in selected:
                rel = ref['path']
                if rel in selected_paths:
                    raise ValueError('duplicate source in allowlist')
                selected_paths.add(rel)
                file = safe_file(root, rel)
                if sha(file.read_bytes()) != ref.get('sha256'):
                    raise ValueError(f'changed material: {rel}')
            validated.append((task, arm, selected))
    # Validate everything before making output. Partial I/O failure leaves an
    # obvious unsealed directory; only a completed control manifest is runnable.
    destination.mkdir(parents=True)
    rng = random.Random(spec['seed'])
    rng.shuffle(validated)
    jobs = []
    for index, (task, arm, selected) in enumerate(validated):
        job_id = sha(canonical([spec['seed'], task['task_id'], arm, spec['model_snapshot']]))[:24]
        home = destination / 'agent_jobs' / job_id
        home.mkdir(parents=True)
        for ref in selected:
            source = safe_file(root, ref['path'])
            data = source.read_bytes()
            if sha(data) != ref['sha256']:
                raise ValueError('material changed between validation and copying')
            target = home / 'material' / ref['path']
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        agent_spec = {'schema': 'plectis-reader-job/1', 'job_id': job_id,
            'prompt': task['prompt'], 'model_snapshot': spec['model_snapshot'],
            'budget': spec['budget'], 'material': selected,
            'output_contract': {'answer': 'text', 'citations': 'list of exact source references',
                                'abstention': 'boolean', 'confidence': 'number in [0,1]'},
            'isolation': 'NOT IMPLEMENTED BY THIS PREPARER; external read-only, no-network, clean-home runner required'}
        write(home / 'job.json', agent_spec)
        jobs.append({'job_id': job_id, 'order': index, 'task_id': task['task_id'],
                     'family_id': task['family_id'], 'world': task.get('world'),
                     'kind': task['kind'], 'arm': arm,
                     'gold_sha256': task['gold_sha256'],
                     'job_spec_sha256': sha(canonical(agent_spec))})
    control = {'schema': 'plectis-reader-control/1', 'mode': mode,
               'study_spec_sha256': sha(canonical(spec)), 'model_snapshot': spec['model_snapshot'],
               'seed': spec['seed'], 'budget': spec['budget'], 'arms': list(arms),
               'analysis_plan': ANALYSIS_PLAN, 'jobs': jobs,
               'boundary': 'preparation receipt only; not registration, execution, grading, or isolation evidence'}
    write(destination / 'private_control.json', control)
    return control


def verify_job(home: Path, expected_spec_sha256: str) -> dict:
    """Bind both the prompt and material allowlist to the trusted control manifest.

    The executor supplies the digest from private_control.json; it must not take
    that value from the mutable job directory that it is checking.
    """
    job = load(home / 'job.json')
    if not re.fullmatch('[a-f0-9]{64}', expected_spec_sha256) or sha(canonical(job)) != expected_spec_sha256:
        raise ValueError('job spec differs from the frozen control manifest')
    for ref in job['material']:
        source = safe_file(home / 'material', ref['path'])
        if sha(source.read_bytes()) != ref['sha256']:
            raise ValueError(f'job material drift: {ref["path"]}')
    return job


def binomial_pmf(n: int, p: float) -> list[float]:
    if n < 0 or not 0 <= p <= 1:
        raise ValueError('invalid binomial parameters')
    if p == 0:
        return [1.0] + [0.0] * n
    if p == 1:
        return [0.0] * n + [1.0]
    logs = [math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)
            + k * math.log(p) + (n - k) * math.log1p(-p) for k in range(n + 1)]
    m = max(logs); values = [math.exp(x - m) for x in logs]; total = math.fsum(values)
    return [v / total for v in values]


def mcnemar_p(b: int, c: int) -> float:
    if min(b, c) < 0:
        raise ValueError('counts must be nonnegative')
    return min(1.0, 2 * math.fsum(binomial_pmf(b + c, .5)[:min(b, c) + 1]))


def exact_power(n: int, delta: float, discordance: float, alpha: float = .05) -> float:
    """Unconditional power of two-sided exact conditional McNemar test.

    b=P(F correct,P wrong)=(q+delta)/2; c=(q-delta)/2.
    Independent task-family pairs are assumed. Within-family repeated prompts
    and extra seeds do not increase this n. This is a planning calculation,
    not an empirical estimate of the system's accuracy or dependence structure.
    """
    if not 0 <= abs(delta) <= discordance <= 1 or not 0 < alpha < 1 or n < 1:
        raise ValueError('invalid power parameters')
    if discordance == 0:
        return 0.0
    weights = binomial_pmf(n, discordance)
    theta = (discordance + delta) / (2 * discordance)
    result = 0.0
    for d, weight in enumerate(weights):
        null = binomial_pmf(d, .5)
        tail = 0.0; k = -1
        for j in range((d + 1) // 2):
            tail += null[j]
            if 2 * tail <= alpha + 1e-14:
                k = j
            else:
                break
        if k >= 0:
            alt = binomial_pmf(d, theta)
            result += weight * (math.fsum(alt[:k + 1]) + math.fsum(alt[d - k:]))
    return result



def conservative_difference_interval(differences: list[int], alpha: float = .05) -> list[float]:
    """Finite-sample bound for an average of independent differences in [-1,1].

    Allocate alpha/2 to a two-sided Hoeffding interval and alpha/2 to a
    no-discordance bound. If all observed differences are zero, independence
    and AM-GM give Pr(all zero) <= (1 - mean discordance probability)**n;
    |mean expected difference| <= mean discordance probability. Intersect
    the two bounds in that case. A union bound gives coverage >= 1-alpha.
    The bound is deliberately conservative and remains nondegenerate in a
    small all-tied cohort. Independence is still required; hashing family IDs
    cannot establish it. No identically distributed item assumption is needed.
    """
    if not differences or not 0 < alpha < 1:
        raise ValueError('nonempty differences and alpha in (0,1) required')
    if any(type(d) is not int or d not in (-1, 0, 1) for d in differences):
        raise ValueError('paired binary differences must be -1, 0, or 1')
    n = len(differences); center = mean(differences)
    radius = math.sqrt(2 * math.log(4 / alpha) / n)
    lo, hi = max(-1.0, center - radius), min(1.0, center + radius)
    if all(d == 0 for d in differences):
        discordance_upper = -math.expm1(math.log(alpha / 2) / n)
        lo, hi = max(lo, -discordance_upper), min(hi, discordance_upper)
    return [lo, hi]

def blind(control: dict, executions: list[dict]) -> dict:
    """Make a grading view; preserve final text, remove explicit arm metadata.

    An execution is {job_id,status,trace_sha256,answer}. Hashes must be supplied
    by Type A's capture owner. This function validates shape, not that external
    hashes resolve. `not_run` is pending, not a scored failure. Arm identity may
    remain inferable from citations: report that partial blinding limitation.
    """
    known = {j['job_id']: j for j in control['jobs']}; seen = set(); packets = []; status_rows = []
    if len(known) != len(control['jobs']):
        raise ValueError('duplicate job in control manifest')
    for e in executions:
        jid = e.get('job_id')
        if jid not in known or jid in seen:
            raise ValueError('unknown or duplicate job execution')
        seen.add(jid)
        status = e.get('status')
        if status not in ('completed', 'timeout', 'budget_exhausted', 'invalid_output', 'not_run'):
            raise ValueError('invalid execution status')
        if status != 'not_run' and not re.fullmatch('[a-f0-9]{64}', e.get('trace_sha256', '')):
            raise ValueError('issued execution needs trace digest')
        item = known[jid]
        status_rows.append({'job_id': jid, 'status': status, 'trace_sha256': e.get('trace_sha256')})
        if status == 'completed':
            if not isinstance(e.get('answer'), str) or not e['answer'].strip():
                raise ValueError('completed execution has no answer')
            packets.append({'grading_id': jid, 'task_id': item['task_id'],
                            'gold_sha256': item['gold_sha256'], 'answer': e['answer']})
    return {'grading_packets': packets, 'private_status': status_rows,
            'missing_job_ids': sorted(set(known) - seen),
            'boundary': 'partially blinded input for independent human grading, no correctness verdict'}


def analyze(control: dict, executions: list[dict], grades: list[dict], baseline='P', treatment='F',
            bootstrap=10000, seed=20260928) -> dict:
    """Intention-to-treat analysis of a COMPLETE issued primary paired cohort.

    Timeout/budget/invalid-output = failure. Missing runs or pending grades are
    an error, never silently dropped. Completed answers require an adjudicated
    binary decision with two independent rater IDs and a native review digest.
    Gold and trace hashes bind grades to the exact answer and frozen task.
    """
    if baseline == treatment or baseline not in ARMS or treatment not in ARMS:
        raise ValueError('baseline and treatment must be distinct supported arms')
    mode = control.get('mode')
    if mode not in ('development', 'confirmatory'):
        raise ValueError('unknown study mode')
    if mode == 'confirmatory' and control.get('analysis_plan') != ANALYSIS_PLAN:
        raise ValueError('confirmatory analysis lacks the frozen F-P primary plan')
    primary = mode == 'confirmatory' and (baseline, treatment) == ('P', 'F')
    blind(control, executions)  # shape and duplicate validation
    issued = {e['job_id']: e for e in executions}; by_grade = {}
    known = {j['job_id']: j for j in control['jobs']}
    for g in grades:
        jid = g.get('job_id')
        if jid not in known or jid in by_grade:
            raise ValueError('unknown or duplicate final adjudication')
        if g.get('final') is not True or type(g.get('correct')) is not bool or type(g.get('severe_error')) is not bool:
            raise ValueError('final adjudication requires binary correct and severe_error')
        raters = g.get('rater_ids')
        if (not isinstance(raters, list) or any(not isinstance(r, str) or not r.strip() for r in raters)
                or len(set(raters)) < 2):
            raise ValueError('two independent grader identities are required')
        if not re.fullmatch('[a-f0-9]{64}', g.get('review_sha256', '')):
            raise ValueError('final review digest required')
        if g.get('gold_sha256') != known[jid]['gold_sha256']:
            raise ValueError('gold digest mismatch')
        if g.get('trace_sha256') != issued.get(jid, {}).get('trace_sha256'):
            raise ValueError('trace digest mismatch')
        if g['correct'] and g['severe_error']:
            raise ValueError('a severe-error answer cannot be wholly correct')
        by_grade[jid] = g
    pairs = defaultdict(dict); worlds = {}; severe = Counter(); stops = Counter()
    for job in control['jobs']:
        arm = job['arm']
        if arm not in (baseline, treatment):
            continue
        e = issued.get(job['job_id'])
        if e is None or e['status'] == 'not_run':
            raise ValueError('primary cohort incomplete; a planned job has not run')
        if e['status'] == 'completed':
            g = by_grade.get(job['job_id'])
            if g is None:
                raise ValueError('completed primary answer awaits independent adjudication')
            y = int(g['correct']); severe[arm] += int(g['severe_error'])
        else:
            y = 0; stops[arm] += 1
        fid = job['family_id']
        if arm in pairs[fid]:
            raise ValueError('repeated family/arm would be pseudoreplication')
        pairs[fid][arm] = y; worlds[fid] = job.get('world', 'unknown')
    if not pairs or any(set(v) != {baseline, treatment} for v in pairs.values()):
        raise ValueError('need complete paired families')
    diffs = {f: ys[treatment] - ys[baseline] for f, ys in pairs.items()}
    b = sum(d == 1 for d in diffs.values()); c = sum(d == -1 for d in diffs.values())
    strata = defaultdict(list)
    for f, d in diffs.items():
        strata[worlds[f]].append(d)
    if bootstrap < 100:
        raise ValueError('at least 100 bootstrap draws required')
    rng = random.Random(seed); draws = []
    for _ in range(bootstrap):
        sample = [rng.choice(ds) for ds in strata.values() for _ in ds]
        draws.append(mean(sample))
    draws.sort()
    # Fixed eight-world estimand; resample independent families within worlds.
    ci = [draws[int(.025 * (bootstrap - 1))], draws[int(.975 * (bootstrap - 1))]]
    conservative_ci = conservative_difference_interval(list(diffs.values()))
    return {'schema': 'plectis-reader-analysis/1', 'mode': mode,
            'families': len(pairs), 'worlds': len(strata), 'baseline': baseline, 'treatment': treatment,
            'analysis_role': ('confirmatory_primary' if primary else
                              'development_descriptive' if mode == 'development' else
                              'secondary_descriptive_no_multiplicity_plan'),
            'baseline_accuracy': mean(v[baseline] for v in pairs.values()),
            'treatment_accuracy': mean(v[treatment] for v in pairs.values()),
            'paired_difference': mean(diffs.values()), 'discordant_treatment_only': b,
            'discordant_baseline_only': c,
            'exact_mcnemar_two_sided_p': mcnemar_p(b, c) if primary else None,
            'family_bootstrap_95_interval': ci,
            'conservative_independent_family_95_interval': conservative_ci,
            'severe_errors_completed_answers': dict(severe), 'stopped_runs_scored_zero': dict(stops),
            'claim_threshold': ANALYSIS_PLAN['minimum_useful_difference'] if primary else None,
            'minimum_useful_effect_ruled_out_by_interval':
                conservative_ci[1] < ANALYSIS_PLAN['minimum_useful_difference'] if primary else None,
            'boundary': ('fixed-corpus decision benchmark; development and secondary estimates are descriptive; '
                         'no novelty or prospective insight conclusion')}


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__); sub = ap.add_subparsers(dest='command', required=True)
    s = sub.add_parser('prepare'); s.add_argument('--spec', type=Path, required=True)
    s.add_argument('--source-root', type=Path, required=True); s.add_argument('--out', type=Path, required=True)
    s = sub.add_parser('verify-job'); s.add_argument('job', type=Path)
    s.add_argument('--expected-spec-sha256', required=True, help='digest from the trusted private control manifest')
    s = sub.add_parser('power'); s.add_argument('--n', type=int, default=352)
    s.add_argument('--delta', type=float, default=.10); s.add_argument('--discordance', type=float, default=.40)
    s = sub.add_parser('blind'); s.add_argument('--control', type=Path, required=True)
    s.add_argument('--executions', type=Path, required=True)
    s = sub.add_parser('analyze'); s.add_argument('--control', type=Path, required=True)
    s.add_argument('--executions', type=Path, required=True); s.add_argument('--grades', type=Path, required=True)
    s.add_argument('--baseline', default='P'); s.add_argument('--treatment', default='F')
    args = ap.parse_args(argv)
    if args.command == 'prepare':
        out = prepare(load(args.spec), args.source_root, args.out)
    elif args.command == 'verify-job':
        out = verify_job(args.job, args.expected_spec_sha256)
    elif args.command == 'power':
        out = {'n': args.n, 'delta': args.delta, 'discordance': args.discordance,
               'exact_power': exact_power(args.n, args.delta, args.discordance)}
    elif args.command == 'blind':
        out = blind(load(args.control), load(args.executions))
    else:
        out = analyze(load(args.control), load(args.executions), load(args.grades), args.baseline, args.treatment)
    print(json.dumps(out, indent=2, ensure_ascii=False))

if __name__ == '__main__':
    main()
