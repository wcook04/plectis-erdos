#!/usr/bin/env python3
"""Read-only journal and attempt instrumentation.
Uses native research_record.replay; creates no new custody or verdict authority.
Reads the explicitly selected, trusted local repository's Python implementation.
Archive availability is not live-main status or a successful Lean compilation.
"""
from __future__ import annotations
import argparse
from collections import Counter
from datetime import datetime
import hashlib
import importlib
import json
import math
from pathlib import Path
import re
import sys
from typing import Any


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(repo: Path, prior: Path | None = None, history: Path | None = None) -> dict:
    repo = repo.resolve(strict=True)
    scripts = str(repo / 'scripts')
    # Refuse accidental reuse of an owner imported from a different checkout.
    prior_module = sys.modules.get('research_record')
    if prior_module and Path(prior_module.__file__).resolve().parent != Path(scripts):
        raise ValueError('research_record was imported from a different checkout; use a fresh process')
    sys.path.insert(0, scripts)
    try:
        native = importlib.import_module('research_record')
    finally:
        sys.path.pop(0)
    events, state = native.replay(repo)
    coverage_path = repo / 'docs/paper_lean_coverage.json'
    claims_path = repo / 'docs/claims.json'
    coverage = json.loads(coverage_path.read_text())
    claims = json.loads(claims_path.read_text())
    rows = coverage.get('rows')
    if rows is None:
        rows = coverage.get('entries')
    if not isinstance(rows, list):
        raise ValueError('unsupported coverage schema; expected rows or entries list')
    claim_rows = claims.get('claims')
    if not isinstance(claim_rows, list):
        raise ValueError('unsupported claims schema')
    latest_review = Counter()
    latest_components = Counter()
    for value in state.returns.values():
        reviews = value['reviews']
        latest_review[reviews[-1]['disposition'] if reviews else 'unreviewed'] += 1
        for d in value['components'].values():
            latest_components[d['decision']] += 1
    outputs = [v['detail'] for v in state.outputs.values()]
    times = Counter(e['recorded_at'] for e in events)
    clock_warning = 'recorded_at is journal insertion time; latency not identified without occurrence receipts'
    result: dict[str, Any] = {
        'schema': 'plectis-snapshot-evidence/1',
        'boundary': 'selected checkout sources; inventory and native journal replay, no causal inference',
        'formal_source': claims.get('release', {}).get('formal_source'),
        'sources': {str(p.relative_to(repo)): sha(p) for p in
                    (coverage_path, claims_path, repo / native.JOURNAL_PATH, Path(native.__file__))},
        'lean_source_files_under_lean': sum(1 for _ in (repo / 'lean').rglob('*.lean')),
        'claim_rows': len(claim_rows),
        'claim_statuses': dict(sorted(Counter(c['status'] for c in claim_rows).items())),
        'coverage_rows': len(rows),
        'lean_coverage_statuses': dict(sorted(Counter(c.get('lean', {}).get('status', 'missing') for c in rows).items())),
        'comparator_statuses': dict(sorted(Counter(c.get('comparator', {}).get('status', 'missing') for c in rows).items())),
        'journal': {'events': len(events), 'rounds': len(state.rounds),
                    'returns_are_artifacts': len(state.returns),
                    'event_kinds': dict(sorted(Counter(e['kind'] for e in events).items())),
                    'native_replay_errors': state.errors,
                    'latest_review_dispositions': dict(sorted(latest_review.items())),
                    'latest_component_dispositions': dict(sorted(latest_components.items())),
                    'outputs': len(outputs),
                    'output_kinds': dict(sorted(Counter(o['kind'] for o in outputs).items())),
                    'outputs_with_producer_links': sum(bool(o['produced_by']) for o in outputs),
                    'recorded_time_range': [min(times), max(times)] if times else None,
                    'largest_same_second_insertions': max(times.values(), default=0),
                    'clock_warning': clock_warning},
        'not_identified': {'new_insight_yield': None, 'semantic_gate_false_admission_rate': None,
                           'return_to_merge_latency': None, 'historical_billed_cost': None}}
    if prior:
        supplied = []
        for p in sorted(prior.rglob('custody_intake.json')):
            data = json.loads(p.read_text())
            supplied.append({'relative_path': str(p.relative_to(prior)), 'sha256': sha(p),
                             'arrival_count': data.get('arrival_count'),
                             'actual_return_rows': len(data.get('returns', []))})
        result['detailed_custody_files_supplied'] = supplied
    if history:
        text = history.read_text()
        m = re.search(r'(\d+)\s+(?:custody\s+)?batches.*?(\d+)\s+returned', text)
        result['history_summary'] = {'sha256': sha(history), 'batches': int(m[1]) if m else None,
                                      'artifact_arrivals': int(m[2]) if m else None,
                                      'boundary': 'summary projection, not all underlying custody records'}
    bp = repo / 'docs/semantic/lab/benchmark_items.json'
    result['existing_benchmark_default_input_present'] = bp.is_file()
    labp = repo / 'docs/theory_lab.json'
    if labp.is_file():
        lab = json.loads(labp.read_text())
        bench = lab.get('benchmark', {})
        result['theory_lab_embedded_benchmark'] = {'items': len(bench.get('items', [])),
            'results': len(bench.get('results', [])),
            'contains_answer_keys': any('answer_key' in r for r in bench.get('items', [])),
            'boundary': 'known development material; never a blind historical-holdout mount'}
    return result


def occurrence(event: Any) -> datetime | None:
    """Only source-backed event-time records can enter latency calculations."""
    if event is None:
        return None
    if not isinstance(event, dict) or event.get('clock_class') != 'contemporaneous_occurrence':
        raise ValueError('event must carry contemporaneous_occurrence clock class')
    if not re.fullmatch(r'[a-f0-9]{64}', str(event.get('evidence_sha256', ''))):
        raise ValueError('event lacks evidence digest')
    value = datetime.fromisoformat(event['occurred_at'].replace('Z', '+00:00'))
    if value.tzinfo is None:
        raise ValueError('event time requires timezone')
    return value


def attempts(rows: list[dict], as_of: str) -> dict:
    """Summarize a reviewed analysis extract bound to native receipt IDs.

    This extract is produced by Type A from owners; this function does not
    validate the external reviews or the bytes named by their digests. A null
    review is unassessed. An empty input identifies no rate. Quantities are
    descriptive. A family id records adjudication, not string-hash equivalence.
    """
    cut = datetime.fromisoformat(as_of.replace('Z', '+00:00'))
    if cut.tzinfo is None:
        raise ValueError('as_of requires timezone')
    seen = set(); cohort = []; relation_counts = Counter(); failed = 0; reviewed = 0
    false_admitted = 0; submitted_duplicates = 0; legitimate = 0; legitimate_admitted = 0
    verified_families = set(); durations = []; mature_30 = 0; landed_30 = 0; clocks_unknown = 0; cost_missing = 0; costs = 0.0
    for r in rows:
        aid = r.get('attempt_id')
        if not isinstance(aid, str) or not aid or aid in seen:
            raise ValueError('attempt IDs must be unique and nonempty; join companion artifacts upstream')
        seen.add(aid)
        if type(r.get('eligible')) is not bool:
            raise ValueError('eligibility must be recorded, not inferred from outcome')
        if not r['eligible']:
            continue
        cohort.append(r)
        review = r.get('review')
        if review is not None:
            if not review.get('receipt_id') or not re.fullmatch('[0-9a-f]{64}', str(review.get('receipt_sha256', ''))):
                raise ValueError('review needs native receipt identity and digest')
            reviewed += 1
            relation = review.get('corpus_relation', 'unknown')
            relation_counts[relation] += 1
            duplicate = relation in ('rediscovery', 'equivalent_restatement')
            submitted_duplicates += duplicate
            false_admitted += duplicate and review.get('admitted_as_progress') is True
            is_legitimate = review.get('legitimate_submission') is True
            legitimate += is_legitimate
            legitimate_admitted += is_legitimate and review.get('accepted_for_appropriate_credit') is True
            if review.get('insight_qualified') is True:
                required = ('mathematical_validity', 'intended_statement', 'corpus_delta_review',
                            'literature_review', 'independent_consumer_use')
                if any(review.get(k) is not True for k in required) or not review.get('family_id'):
                    raise ValueError('qualified insight lacks explicit reviewed axes or family id')
                verified_families.add(review['family_id'])
        start = occurrence(r.get('received')); end = occurrence(r.get('landed'))
        if start and start > cut:
            raise ValueError('cohort contains a future arrival')
        if start is None:
            clocks_unknown += 1
        else:
            if end and end < start:
                raise ValueError('landing precedes receipt')
            observed = end is not None and end <= cut
            duration = ((end if observed else cut) - start).total_seconds()
            mature = (cut - start).total_seconds() >= 30 * 86400
            mature_30 += int(mature)
            landed_30 += int(mature and observed and duration <= 30 * 86400)
            durations.append({'attempt_id': aid, 'seconds': duration, 'landed_by_cutoff': observed,
                              'mature_30_day_cohort': mature})
        cost = r.get('billed_usd')
        if cost is None:
            cost_missing += 1
        elif isinstance(cost, bool) or not isinstance(cost, (int, float)) or not math.isfinite(cost) or cost < 0:
            raise ValueError('invalid billed cost')
        else:
            costs += cost
    n = len(cohort)
    ratio = lambda a, b: a / b if b else None
    return {'schema': 'plectis-attempt-evidence/1', 'eligible_attempts': n,
            'reviewed_attempts': reviewed, 'review_missing': n - reviewed,
            'corpus_relation_counts_among_reviewed': dict(relation_counts),
            'rediscovery_or_equivalent_rate_among_reviewed': ratio(submitted_duplicates, reviewed),
            'false_admission_rate_among_reviewed': ratio(false_admitted, reviewed),
            'false_admission_rate_among_known_duplicate_submissions': ratio(false_admitted, submitted_duplicates),
            'legitimate_acceptance_rate': ratio(legitimate_admitted, legitimate),
            'qualified_insight_families_observed': len(verified_families),
            'qualified_insight_families_per_100_eligible_attempts': ratio(100 * len(verified_families), n),
            'insight_yield_complete_review': n > 0 and reviewed == n,
            'known_clock_durations_with_censor_flags': durations,
            'clock_missing': clocks_unknown,
            'mature_30_day_attempts': mature_30,
            'landed_by_30_days_in_mature_cohort': landed_30,
            'mature_cohort_30_day_landing_rate': ratio(landed_30, mature_30),
            'billed_usd_observed_subtotal': costs,
            'billed_usd_complete_total': costs if n and not cost_missing else None,
            'cost_missing': cost_missing,
            'boundary': 'source-bound reviewed extract required; no causal attribution; censored waits are retained'}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='command', required=True)
    a = sub.add_parser('snapshot'); a.add_argument('--repo', type=Path, required=True)
    a.add_argument('--prior', type=Path); a.add_argument('--history', type=Path)
    a = sub.add_parser('attempts'); a.add_argument('--input', type=Path, required=True)
    a.add_argument('--as-of', required=True)
    args = ap.parse_args()
    if args.command == 'snapshot':
        result = snapshot(args.repo, args.prior, args.history)
    else:
        result = attempts([json.loads(s) for s in args.input.read_text().splitlines() if s.strip()], args.as_of)
    print(json.dumps(result, indent=2, ensure_ascii=False))

if __name__ == '__main__':
    main()
