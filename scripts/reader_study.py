#!/usr/bin/env python3
"""Native reader study preparation, bounded trusted bridge, capture, and analysis.

Execution requires an operator-authorized, reviewed provider bridge; this module
does not provide an OS sandbox, authenticate provider usage, grade mathematics,
or declare preregistration. All study outputs stay outside the source tree.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import hashlib
import json
import math
import os
import stat
import subprocess
import time
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
    if not relative or rel.is_absolute() or '..' in rel.parts or '\\' in relative or str(rel) != relative:
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
        if not task.get('prompt') or task.get('kind') not in ('frontier', 'restatement', 'status', 'transfer', 'paper'):
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
    material = home / 'material'
    if material.is_symlink() or not material.is_dir():
        raise ValueError('material root must be a real directory')
    expected = {ref['path'] for ref in job['material']}
    if len(expected) != len(job['material']):
        raise ValueError('duplicate material path in frozen job')
    expected_dirs = {str(parent) for name in expected
                     for parent in PurePosixPath(name).parents if str(parent) != '.'}
    actual = set(); actual_dirs = set()
    def walk_error(error: OSError) -> None:
        raise error
    for directory, dirs, names in os.walk(material, followlinks=False, onerror=walk_error):
        for name in dirs:
            child = Path(directory) / name
            actual_dirs.add(child.relative_to(material).as_posix())
            if child.is_symlink():
                raise ValueError('symlink directory in material tree')
        for name in names:
            child = Path(directory) / name
            if not stat.S_ISREG(child.lstat().st_mode):
                raise ValueError('non-regular file in material tree')
            actual.add(child.relative_to(material).as_posix())
    if actual != expected or actual_dirs != expected_dirs:
        raise ValueError('material inventory differs from frozen allowlist')
    for ref in job['material']:
        source = safe_file(material, ref['path'])
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
    singleton_worlds = sorted(str(world) for world, ds in strata.items() if len(ds) < 2)
    ci = (None if singleton_worlds else
          [draws[int(.025 * (bootstrap - 1))], draws[int(.975 * (bootstrap - 1))]])
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
            'family_bootstrap_status': ('not_estimable_singleton_world' if singleton_worlds
                                        else 'resampled_within_world'),
            'singleton_worlds': singleton_worlds,
            'conservative_independent_family_95_interval': conservative_ci,
            'severe_errors_completed_answers': dict(severe), 'stopped_runs_scored_zero': dict(stops),
            'claim_threshold': ANALYSIS_PLAN['minimum_useful_difference'] if primary else None,
            'minimum_useful_effect_ruled_out_by_interval':
                conservative_ci[1] < ANALYSIS_PLAN['minimum_useful_difference'] if primary else None,
            'boundary': ('fixed-corpus decision benchmark; development and secondary estimates are descriptive; '
                         'no novelty or prospective insight conclusion')}


def _strict_json(raw: str) -> Any:
    """Parse controller input without duplicate keys or nonfinite numbers."""
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f'duplicate JSON key: {key}')
            result[key] = value
        return result
    def finite_float(value):
        number = float(value)
        if not math.isfinite(number):
            raise ValueError('nonfinite JSON number')
        return number
    return json.loads(raw, object_pairs_hook=pairs, parse_float=finite_float,
                      parse_constant=lambda value: (_ for _ in ()).throw(
                          ValueError(f'nonfinite JSON number: {value}')))


def _file_sha(path: Path) -> str:
    return sha(path.read_bytes())


def _bound_study(control_path: Path, spec_path: Path,
                 expected_control_sha256: str, expected_spec_sha256: str) -> tuple[dict, dict]:
    for expected, path in ((expected_control_sha256, control_path),
                           (expected_spec_sha256, spec_path)):
        if not re.fullmatch(r'[a-f0-9]{64}', expected) or path.is_symlink() or _file_sha(path) != expected:
            raise ValueError(f'externally pinned study file changed: {path.name}')
    control = _strict_json(control_path.read_text())
    spec = _strict_json(spec_path.read_text())
    if (control.get('schema') != 'plectis-reader-control/1' or
            spec.get('schema') != 'plectis-reader-study/1' or
            control.get('study_spec_sha256') != sha(canonical(spec)) or
            control.get('model_snapshot') != spec.get('model_snapshot') or
            control.get('mode') != 'development' or spec.get('mode') != 'development'):
        raise ValueError('study spec/control identity or development mode mismatch')
    if not re.fullmatch(r'[0-9a-f]{40}', spec.get('source_commit', '')):
        raise ValueError('exact source commit required for execution')
    jobs = control.get('jobs')
    if not isinstance(jobs, list) or not jobs or len({j['job_id'] for j in jobs}) != len(jobs):
        raise ValueError('control jobs missing, empty, or duplicated')
    return control, spec


def _safe_receipt_file(root: Path, relative: str) -> Path:
    if not isinstance(relative, str) or not relative or '\\' in relative:
        raise ValueError('unsafe receipt locator')
    rel = PurePosixPath(relative)
    if rel.is_absolute() or '..' in rel.parts or str(rel) != relative:
        raise ValueError('unsafe receipt locator')
    path = root
    for part in rel.parts:
        path = path / part
        if path.is_symlink():
            raise ValueError('linked receipt path')
    if not path.is_file():
        raise ValueError('missing receipt file')
    path.resolve().relative_to(root.resolve())
    return path


def _structured_answer(value: Any, budget: dict) -> str:
    if not isinstance(value, dict) or set(value) != {'answer', 'citations', 'abstention', 'confidence'}:
        raise ValueError('invalid structured final')
    if not isinstance(value['answer'], str) or not value['answer'].strip() or len(value['answer'].split()) > 650:
        raise ValueError('missing or oversized answer')
    if not isinstance(value['citations'], list) or any(not isinstance(x, str) or not x.strip()
                                                       for x in value['citations']):
        raise ValueError('invalid citations')
    if type(value['abstention']) is not bool or type(value['confidence']) not in (int, float) or not 0 <= value['confidence'] <= 1:
        raise ValueError('invalid abstention/confidence')
    result = json.dumps(value, sort_keys=True, ensure_ascii=False, allow_nan=False)
    if len(result.encode()) > budget['max_final_bytes']:
        raise ValueError('structured final exceeds byte budget')
    return result


class _ReadOnlyBroker:
    """Only explicit list/read/literal-search over a verified job allowlist."""
    def __init__(self, home: Path, job: dict):
        self.home = home
        self.job = job
        self.files = {ref['path']: ref['sha256'] for ref in job['material']}
        self.calls = 0
        self.bytes = 0
        self.started = time.monotonic()

    def _text(self, relative: str) -> str:
        if relative not in self.files:
            raise ValueError('path outside job allowlist')
        path = safe_file(self.home / 'material', relative)
        raw = path.read_bytes()
        if sha(raw) != self.files[relative]:
            raise ValueError('material changed during read')
        if relative.endswith('.gz'):
            import gzip
            import io
            with gzip.GzipFile(fileobj=io.BytesIO(raw)) as stream:
                raw = stream.read(128 * 1024 * 1024 + 1)
            if len(raw) > 128 * 1024 * 1024:
                raise ValueError('decompressed source limit exceeded')
        return raw.decode('utf-8')

    def request(self, request: dict) -> dict:
        budget = self.job['budget']
        self.calls += 1
        try:
            if self.calls > budget['max_tool_calls'] or time.monotonic() - self.started > budget['wall_seconds']:
                raise ValueError('broker budget exhausted')
            if not isinstance(request, dict):
                raise ValueError('tool request must be object')
            op = request.get('op')
            allowed = {'list': {'op', 'prefix', 'offset', 'limit'},
                       'read': {'op', 'path', 'start_line', 'max_lines'},
                       'search': {'op', 'query', 'prefix', 'limit'}}
            if op not in allowed or set(request) - allowed[op]:
                raise ValueError('only list/read/literal-search allowed')
            prefix = request.get('prefix', '')
            if not isinstance(prefix, str) or prefix.startswith('/') or '..' in PurePosixPath(prefix).parts:
                raise ValueError('unsafe tool prefix')
            if op == 'list':
                paths = sorted(p for p in self.files if p.startswith(prefix))
                offset = request.get('offset', 0); limit = request.get('limit', 30)
                if type(offset) is not int or not 0 <= offset <= len(paths) or type(limit) is not int or not 1 <= limit <= 100:
                    raise ValueError('invalid list bounds')
                result = {'paths': paths[offset:offset + limit], 'total': len(paths)}
            elif op == 'read':
                path = request['path']; lines = self._text(path).splitlines()
                start = request.get('start_line', 1); count = request.get('max_lines', 80)
                if type(start) is not int or start < 1 or type(count) is not int or not 1 <= count <= 200:
                    raise ValueError('invalid read bounds')
                result = {'path': path, 'source_sha256': self.files[path],
                          'text': '\n'.join(f'{i}: {line}' for i, line in
                                            enumerate(lines[start - 1:start - 1 + count], start))[:12000]}
            else:
                query = request.get('query'); limit = request.get('limit', 12)
                if not isinstance(query, str) or not 1 <= len(query) <= 200 or type(limit) is not int or not 1 <= limit <= 20:
                    raise ValueError('invalid search bounds')
                rows = []
                for path in sorted(self.files):
                    if not path.startswith(prefix):
                        continue
                    body = self._text(path)
                    position = body.find(query)
                    if position >= 0:
                        rows.append({'path': path, 'line': body.count('\n', 0, position) + 1,
                                     'source_sha256': self.files[path],
                                     'excerpt': body[max(0, position - 100):position + len(query) + 220]})
                    if len(rows) >= limit:
                        break
                result = {'matches': rows, 'search': 'literal'}
            response = {'ok': True, 'result': result}
        except (ValueError, KeyError, TypeError, OSError, UnicodeError) as exc:
            response = {'ok': False, 'error': str(exc)}
        encoded = canonical(response)
        if len(encoded) > budget['max_tool_response_bytes']:
            response = {'ok': False, 'error': 'tool response byte limit exceeded'}
            encoded = canonical(response)
        if self.bytes + len(encoded) > budget['max_total_tool_response_bytes']:
            return {'ok': False, 'error': 'cumulative tool response budget exhausted'}
        self.bytes += len(encoded)
        return response


def execute_job(control_path: Path, spec_path: Path, expected_control_sha256: str,
                expected_spec_sha256: str, job_id: str, deployment: Path,
                out: Path, *, synthetic: bool = False, authorize_provider_run: bool = False) -> dict:
    """Run one trusted bridge. This is no sandbox or independent provider attestation."""
    if out.exists():
        raise ValueError('refuse to overwrite issued run')
    control, spec = _bound_study(control_path, spec_path, expected_control_sha256, expected_spec_sha256)
    jobs = {j['job_id']: j for j in control['jobs']}
    if job_id not in jobs:
        raise ValueError('unknown job')
    cfg = _strict_json(deployment.read_text())
    deployment_sha = _file_sha(deployment)
    if cfg.get('model_snapshot') != control['model_snapshot']:
        raise ValueError('deployment model differs from frozen study')
    if synthetic:
        if not control['model_snapshot'].startswith('SYNTHETIC'):
            raise ValueError('synthetic mode requires an explicitly synthetic study')
    else:
        binding = spec.get('real_binding', {})
        if (not authorize_provider_run or control['model_snapshot'].startswith('SYNTHETIC') or
                spec.get('review_status') is None or
                binding.get('deployment_config_sha256') != deployment_sha or
                not binding.get('semantic_review_sha256') or
                cfg.get('operator_reviewed') is not True or
                cfg.get('only_tools') != ['list', 'read', 'search'] or
                cfg.get('arbitrary_execution') is not False or
                cfg.get('clean_session_per_job') is not True or
                any(not cfg.get(k) for k in ('provider', 'controller_identity',
                                            'status_capture_policy', 'usage_enforcement_policy'))):
            raise ValueError('real provider run lacks reviewed, budget-bound deployment')
    argv = cfg.get('client_command')
    if not isinstance(argv, list) or not argv or any(not isinstance(x, str) or not x for x in argv):
        raise ValueError('trusted client command argv required')
    home = control_path.parent / 'agent_jobs' / job_id
    job = verify_job(home, jobs[job_id]['job_spec_sha256'])
    budget = job['budget']; broker = _ReadOnlyBroker(home, job)
    for field in ('wall_seconds', 'max_model_requests', 'max_tool_calls', 'max_total_input_tokens',
                  'max_total_output_tokens', 'max_final_bytes', 'max_tool_response_bytes',
                  'max_total_tool_response_bytes'):
        if type(budget.get(field)) is not int or budget[field] <= 0:
            raise ValueError('controller requires all positive resource bounds')
    out.mkdir(parents=True)
    trace = out / 'trace.jsonl'; start = time.monotonic()
    requests = 0; coverage = 0; used_in = 0; used_out = 0; provider_ids = []
    history = [{'role': 'user', 'content': job['prompt']}]
    status = 'invalid_output'; reason = 'no final answer'
    def event(value):
        value['controller_monotonic_elapsed_seconds'] = time.monotonic() - start
        value['synthetic'] = synthetic
        with trace.open('a', encoding='utf-8') as stream:
            stream.write(json.dumps(value, ensure_ascii=False, allow_nan=False) + '\n')
    identity = {'job_id': job_id, 'job_spec_sha256': jobs[job_id]['job_spec_sha256'],
                'expected_control_sha256': expected_control_sha256,
                'expected_spec_sha256': expected_spec_sha256,
                'model_snapshot': control['model_snapshot'],
                'source_commit': spec['source_commit'],
                'deployment_sha256': deployment_sha,
                'origin': 'synthetic' if synthetic else 'real'}
    event({'type': 'controller_start', **identity, 'budget': budget})
    try:
        while requests < budget['max_model_requests']:
            remaining = budget['wall_seconds'] - (time.monotonic() - start)
            if remaining <= 0:
                status = 'timeout'; reason = 'job wall-clock cap'; break
            requests += 1
            request = {'schema': 'plectis-reader-provider-request/1',
                       'model_snapshot': control['model_snapshot'],
                       'generation_parameters': cfg.get('generation_parameters', {}),
                       'history': history, 'tools': ['list', 'read', 'search'],
                       'remaining_input_tokens': budget['max_total_input_tokens'] - used_in,
                       'remaining_output_tokens': budget['max_total_output_tokens'] - used_out,
                       'max_final_bytes': budget['max_final_bytes']}
            if request['remaining_input_tokens'] <= 0 or request['remaining_output_tokens'] <= 0:
                status = 'budget_exhausted'; reason = 'token cap'; break
            event({'type': 'provider_request', 'index': requests, 'request': request})
            result = subprocess.run(argv, input=json.dumps(request), text=True,
                                    capture_output=True, timeout=remaining, check=False)
            event({'type': 'provider_response', 'index': requests,
                   'returncode': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr})
            if result.returncode:
                reason = 'bridge nonzero exit'; break
            response = _strict_json(result.stdout)
            if not isinstance(response, dict) or response.get('request_admitted_within_limits') is not True:
                reason = 'bridge did not attest pre-request admission'; break
            usage = response.get('usage', {})
            token_fields = ('input_tokens', 'output_tokens', 'cache_read_input_tokens', 'cache_creation_input_tokens')
            if not isinstance(usage, dict) or any(type(usage.get(k)) is not int or usage[k] < 0 for k in token_fields):
                reason = 'missing usage prevents bounded execution'; break
            used_in += usage['input_tokens'] + usage['cache_read_input_tokens'] + usage['cache_creation_input_tokens']
            used_out += usage['output_tokens']; coverage += 1
            provider_id = response.get('provider_run_id')
            if not synthetic and (not isinstance(provider_id, str) or not provider_id.strip()):
                reason = 'real bridge response lacks provider run identity'; break
            if provider_id is not None:
                provider_ids.append(provider_id)
            event({'type': 'assistant', 'message': {'role': 'assistant',
                   'id': f'controller-{job_id}-{requests}', 'model': control['model_snapshot'],
                   'usage': usage, 'content': []}, 'provider_run_id': response.get('provider_run_id')})
            if used_in > budget['max_total_input_tokens'] or used_out > budget['max_total_output_tokens']:
                status = 'budget_exhausted'; reason = 'bridge token-admission violation'; break
            final = response.get('final'); calls = response.get('tool_calls', [])
            if final is not None and calls:
                reason = 'bridge supplied both final and tool calls'; break
            if final is not None:
                _structured_answer(final, budget)
                event({'type': 'attachment', 'attachment': {'type': 'structured_output', 'data': final}})
                status = 'completed'; reason = 'one accepted final'; break
            if not isinstance(calls, list) or not calls:
                reason = 'bridge supplied neither final nor tools'; break
            history.append({'role': 'assistant', 'tool_calls': calls})
            for call in calls:
                answer = broker.request(call)
                event({'type': 'broker_exchange', 'request': call, 'response': answer})
                history.append({'role': 'tool', 'request': call, 'content': answer})
                if broker.calls >= budget['max_tool_calls'] or broker.bytes >= budget['max_total_tool_response_bytes']:
                    status = 'budget_exhausted'; reason = 'tool budget'; break
            if status == 'budget_exhausted':
                break
        else:
            status = 'budget_exhausted'; reason = 'model request cap'
    except subprocess.TimeoutExpired:
        status = 'timeout'; reason = 'bridge terminated at wall-clock cap'
    except (ValueError, KeyError, TypeError, OSError) as exc:
        status = 'invalid_output'; reason = str(exc)
    try:
        verify_job(home, jobs[job_id]['job_spec_sha256'])
    except (ValueError, OSError):
        status = 'invalid_output'; reason = 'material changed during execution'
        event({'type': 'integrity_failure', 'reason': reason})
    event({'type': 'controller_stop', 'status': status, 'reason': reason})
    receipt = {'schema': 'plectis-reader-controller-receipt/1', **identity,
               'status': status, 'provider_run_id': provider_ids[0] if provider_ids else None,
               'raw_trace_path': 'trace.jsonl',
               'raw_trace_sha256': _file_sha(trace), 'bridge_requests': requests,
               'usage_response_coverage': [coverage, requests],
               'reported_usage': {'input_tokens_including_cache': used_in if coverage == requests else None,
                                  'output_tokens': used_out if coverage == requests else None},
               'terminal_status_evidence': reason, 'actual_billed_cost': None,
               'boundary': 'Bridge admission and usage are trusted assertions, not provider verification.'}
    write(out / 'receipt.json', receipt)
    return receipt


def _check_completed_accounting(rows: list[dict], receipt: dict, job: dict,
                                job_id: str, final_event: dict) -> None:
    """Check the complete bridge request/response/usage chain, not just counts."""
    requests = [(i, row) for i, row in enumerate(rows) if row.get('type') == 'provider_request']
    responses = [(i, row) for i, row in enumerate(rows) if row.get('type') == 'provider_response']
    assistants = [(i, row) for i, row in enumerate(rows) if row.get('type') == 'assistant']
    count = len(requests)
    if not count or len(responses) != count or len(assistants) != count:
        raise ValueError('completed run lacks one response and assistant per request')
    if receipt.get('bridge_requests') != count or receipt.get('usage_response_coverage') != [count, count]:
        raise ValueError('completed run receipt request/usage coverage mismatch')
    if final_event not in rows or rows.index(final_event) <= assistants[-1][0]:
        raise ValueError('accepted final does not follow the provider response')
    token_fields = ('input_tokens', 'output_tokens', 'cache_read_input_tokens',
                    'cache_creation_input_tokens')
    budget = job['budget']; used_in = used_out = 0
    for number, ((qi, request_event), (ri, response_event), (ai, assistant_event)) in enumerate(
            zip(requests, responses, assistants, strict=True), 1):
        if not qi < ri < ai or (number < count and ai >= requests[number][0]):
            raise ValueError('provider lifecycle event ordering differs')
        if request_event.get('index') != number or response_event.get('index') != number:
            raise ValueError('provider request/response indices differ')
        request = request_event.get('request')
        if (not isinstance(request, dict) or
                request.get('schema') != 'plectis-reader-provider-request/1' or
                request.get('model_snapshot') != receipt['model_snapshot'] or
                request.get('tools') != ['list', 'read', 'search'] or
                request.get('remaining_input_tokens') != budget['max_total_input_tokens'] - used_in or
                request.get('remaining_output_tokens') != budget['max_total_output_tokens'] - used_out or
                request.get('max_final_bytes') != budget['max_final_bytes']):
            raise ValueError('provider request differs from remaining frozen budget')
        if response_event.get('returncode') != 0:
            raise ValueError('completed run contains failed bridge response')
        response = _strict_json(response_event.get('stdout', ''))
        if not isinstance(response, dict) or response.get('request_admitted_within_limits') is not True:
            raise ValueError('bridge response lacks pre-request admission')
        usage = response.get('usage')
        if not isinstance(usage, dict) or any(type(usage.get(k)) is not int or usage[k] < 0
                                                for k in token_fields):
            raise ValueError('completed bridge usage missing or invalid')
        message = assistant_event.get('message')
        if (not isinstance(message, dict) or message.get('role') != 'assistant' or
                message.get('id') != f'controller-{job_id}-{number}' or
                message.get('model') != receipt['model_snapshot'] or
                message.get('usage') != usage or
                assistant_event.get('provider_run_id') != response.get('provider_run_id')):
            raise ValueError('assistant identity or usage differs from bridge response')
        used_in += usage['input_tokens'] + usage['cache_read_input_tokens'] + usage['cache_creation_input_tokens']
        used_out += usage['output_tokens']
        if used_in > budget['max_total_input_tokens'] or used_out > budget['max_total_output_tokens']:
            raise ValueError('completed run exceeded frozen token budget')
        if number < count and response.get('final') is not None:
            raise ValueError('accepted final preceded last provider request')
        if number == count and response.get('final') != final_event['attachment'].get('data'):
            raise ValueError('accepted final differs from bridge response')
    if receipt.get('reported_usage') != {'input_tokens_including_cache': used_in,
                                          'output_tokens': used_out}:
        raise ValueError('controller reported usage differs from checked bridge events')
    if receipt.get('provider_run_id') != assistants[0][1].get('provider_run_id'):
        raise ValueError('controller provider identity differs from bridge events')


def capture_jobs(control_path: Path, spec_path: Path, expected_control_sha256: str,
                 expected_spec_sha256: str, index: Path, out: Path,
                 *, synthetic: bool = False) -> dict:
    """Admit complete controller-issued traces; never accept bare final attachments."""
    import reader_trace_adapter
    if out.exists():
        raise ValueError('refuse to overwrite capture')
    control, spec = _bound_study(control_path, spec_path, expected_control_sha256, expected_spec_sha256)
    if not synthetic and control['model_snapshot'].startswith('SYNTHETIC'):
        raise ValueError('provider-unbound template cannot capture real runs')
    entries = _strict_json(index.read_text())
    if not isinstance(entries, list):
        raise ValueError('capture index must be a list')
    jobs = {j['job_id']: j for j in control['jobs']}
    seen_jobs = set(); seen_traces = set(); seen_receipts = set(); executions = []; bindings = []
    for entry in entries:
        jid = entry.get('job_id')
        if jid not in jobs or jid in seen_jobs:
            raise ValueError('unknown or duplicate capture job')
        seen_jobs.add(jid)
        receipt_path = _safe_receipt_file(index.parent, entry.get('controller_receipt_path'))
        receipt_sha = _file_sha(receipt_path)
        if receipt_sha != entry.get('controller_receipt_sha256') or receipt_sha in seen_receipts:
            raise ValueError('controller receipt changed or reused')
        seen_receipts.add(receipt_sha)
        receipt = _strict_json(receipt_path.read_text())
        if receipt.get('schema') != 'plectis-reader-controller-receipt/1':
            raise ValueError('capture requires a native controller receipt')
        trace = _safe_receipt_file(receipt_path.parent, receipt.get('raw_trace_path'))
        trace_sha = _file_sha(trace)
        if trace_sha != receipt.get('raw_trace_sha256') or trace_sha in seen_traces:
            raise ValueError('trace changed or reused')
        seen_traces.add(trace_sha)
        expected = {'job_id': jid, 'job_spec_sha256': jobs[jid]['job_spec_sha256'],
                    'expected_control_sha256': expected_control_sha256,
                    'expected_spec_sha256': expected_spec_sha256,
                    'model_snapshot': control['model_snapshot'],
                    'source_commit': spec['source_commit'],
                    'origin': 'synthetic' if synthetic else 'real'}
        for key, value in expected.items():
            if receipt.get(key) != value:
                raise ValueError(f'controller receipt {key} mismatch')
        if not synthetic and receipt.get('deployment_sha256') != spec.get('real_binding', {}).get('deployment_config_sha256'):
            raise ValueError('controller deployment differs from reviewed study')
        job = verify_job(control_path.parent / 'agent_jobs' / jid, jobs[jid]['job_spec_sha256'])
        rows = [_strict_json(line) for line in trace.read_text().splitlines() if line.strip()]
        if not rows or any(type(row) is not dict for row in rows):
            raise ValueError('empty or malformed controller trace')
        if any(row.get('synthetic') is not synthetic for row in rows):
            raise ValueError('trace origin flag differs from capture mode')
        starts = [r for r in rows if r.get('type') == 'controller_start']
        stops = [r for r in rows if r.get('type') == 'controller_stop']
        if len(starts) != 1 or len(stops) != 1 or rows[0] is not starts[0] or rows[-1] is not stops[0]:
            raise ValueError('incomplete controller lifecycle')
        for key, value in {**expected, 'deployment_sha256': receipt['deployment_sha256'],
                           'budget': job['budget']}.items():
            if starts[0].get(key) != value:
                raise ValueError(f'controller start {key} mismatch')
        if stops[0].get('status') != receipt.get('status') or stops[0].get('reason') != receipt.get('terminal_status_evidence'):
            raise ValueError('controller stop/receipt mismatch')
        requests = [r for r in rows if r.get('type') == 'provider_request']
        responses = [r for r in rows if r.get('type') == 'provider_response']
        if len(requests) != receipt.get('bridge_requests') or len(responses) > len(requests):
            raise ValueError('provider request accounting mismatch')
        status = receipt.get('status')
        if status not in ('completed', 'timeout', 'budget_exhausted', 'invalid_output'):
            raise ValueError('unknown terminal status')
        final_events = [r for r in rows if r.get('type') == 'attachment' and
                        isinstance(r.get('attachment'), dict) and r['attachment'].get('type') == 'structured_output']
        norm = reader_trace_adapter.normalize(rows)
        execution = {'job_id': jid, 'status': status, 'trace_sha256': trace_sha}
        if status == 'completed':
            if not synthetic:
                ids = [r.get('provider_run_id') for r in rows if r.get('type') == 'assistant']
                if not isinstance(receipt.get('provider_run_id'), str) or receipt['provider_run_id'] not in ids:
                    raise ValueError('completed real run lacks bound provider identity')
            if len(final_events) != 1:
                raise ValueError('completed run needs exactly one accepted final')
            _check_completed_accounting(rows, receipt, job, jid, final_events[0])
            execution['answer'] = _structured_answer(norm['structured_final'], control['budget'])
        elif final_events:
            raise ValueError('failed terminal state carries accepted final')
        executions.append(execution)
        bindings.append({'job_id': jid, 'controller_receipt_sha256': receipt_sha,
                         'trace_sha256': trace_sha, 'source_commit': spec['source_commit'],
                         'model_snapshot': control['model_snapshot'],
                         'boundary': 'Lifecycle bound to native controller bytes; host and provider remain trusted.'})
    if seen_jobs != set(jobs):
        raise ValueError('issued cohort incomplete')
    out.mkdir(parents=True)
    write(out / 'executions.json', executions)
    write(out / 'capture_receipt.json', {'schema': 'plectis-reader-capture/1',
          'synthetic': synthetic, 'source_commit': spec['source_commit'],
          'index_sha256': _file_sha(index), 'executions_sha256': _file_sha(out / 'executions.json'),
          'bindings': bindings, 'provider_execution_verified_here': False,
          'independent_grading_status': 'pending'})
    return {'executions': len(executions), 'synthetic': synthetic,
            'capture_receipt_sha256': _file_sha(out / 'capture_receipt.json')}


def main(argv: list[str] | None = None) -> None:
    import sys
    actual = list(sys.argv[1:] if argv is None else argv)
    if actual and actual[0].startswith('paper-'):
        from reader_paper_protocol import main as paper_main
        paper_main(actual)
        return
    ap = argparse.ArgumentParser(description=__doc__); sub = ap.add_subparsers(dest='command', required=True)
    s = sub.add_parser('prepare'); s.add_argument('--spec', type=Path, required=True)
    s.add_argument('--source-root', type=Path, required=True); s.add_argument('--out', type=Path, required=True)
    s = sub.add_parser('execute'); s.add_argument('--control', type=Path, required=True)
    s.add_argument('--spec', type=Path, required=True); s.add_argument('--expected-control-sha256', required=True)
    s.add_argument('--expected-spec-sha256', required=True); s.add_argument('--job-id', required=True)
    s.add_argument('--deployment', type=Path, required=True); s.add_argument('--out', type=Path, required=True)
    s.add_argument('--synthetic', action='store_true'); s.add_argument('--authorize-provider-run', action='store_true')
    s = sub.add_parser('capture'); s.add_argument('--control', type=Path, required=True)
    s.add_argument('--spec', type=Path, required=True); s.add_argument('--expected-control-sha256', required=True)
    s.add_argument('--expected-spec-sha256', required=True); s.add_argument('--index', type=Path, required=True)
    s.add_argument('--out', type=Path, required=True); s.add_argument('--synthetic', action='store_true')
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
    elif args.command == 'execute':
        out = execute_job(args.control, args.spec, args.expected_control_sha256,
                          args.expected_spec_sha256, args.job_id, args.deployment,
                          args.out, synthetic=args.synthetic,
                          authorize_provider_run=args.authorize_provider_run)
    elif args.command == 'capture':
        out = capture_jobs(args.control, args.spec, args.expected_control_sha256,
                           args.expected_spec_sha256, args.index, args.out,
                           synthetic=args.synthetic)
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
