#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Proposed sibling of query_continuations.py; native-owner extension, not a graph.

Classify a recorded cross-problem reduction's obligations by calling the EXISTING
Graph.frontier().check. A conditional edge is not a successful transfer. Keep
positive/negative logical transport separate from feasibility and usefulness.
Native graph admission (pin, import closure, exporter receipt) is the caller's job.
This helper never promotes an input graph to current authority.
"""
from __future__ import annotations
from collections import Counter
from typing import Any

def classify(graph: Any, row: dict[str, Any], *, max_work: int=10000,
             run_joint_check: bool=True) -> dict[str, Any]:
    if max_work < 0:
        raise ValueError('negative work budget')
    target=graph.canon(row['supplies'])
    # Legacy cmd_transfer calls all nonsupplied residuals "open". Some are refuted.
    residuals=sorted({graph.canon(k) for k in row['open_residuals']})
    known=set(graph.statements)
    unknown=[k for k in [target,*residuals] if k not in known]
    ans={'residual_statuses':{k:graph.status(k) if k in known else 'unknown_key' for k in residuals},
         'refuted_residuals':[k for k in residuals if k in graph.refuted],
         'satisfiability':'not_established','usefulness':'not_measured',
         'novelty':'not_assessed','evidence_class':'derivation_over_recorded_edges'}
    if getattr(graph,'inconsistent',[]):
        return {**ans,'decision':'base_graph_inconsistent'}
    if unknown:
        return {**ans,'decision':'unknown_key','unknown_keys':unknown}
    if ans['refuted_residuals']:
        return {**ans,'decision':'refuted_residual'}
    if not run_joint_check:
        return {**ans,'decision':'unknown_budget','budget_reason':'joint_check_count'}
    check=graph.frontier().check(residuals,target=target,max_work=max_work,witnesses=False)
    if check['status'] in ('refuted_jointly','base_graph_inconsistent'):
        decision=check['status']
    elif check.get('endpoint_relation')=='joint_endpoint_equivalence':
        decision='endpoint_equivalent'
    elif check['status']=='unknown_budget' or check.get('endpoint_relation')=='unknown_budget':
        decision='unknown_budget'
    elif target in graph.supplied:
        decision='already_supplied'
    else:
        decision='candidate_not_proved_useful'
    return {**ans,'decision':decision,'joint_check':check}

def screen(graph: Any, rows: list[dict[str, Any]], *, max_work: int=10000,
           max_checks: int=250) -> dict[str, Any]:
    if max_work < 0 or max_checks < 0:
        raise ValueError('negative budget')
    counts: Counter[str]=Counter(); result=[]; checks=0
    for row in rows:
        # Refuted-residual and malformed-key screens do not spend a closure call.
        r=classify(graph,row,max_work=max_work,run_joint_check=checks<max_checks)
        if 'joint_check' in r: checks+=1
        counts[r['decision']]+=1
        result.append({**row,'obligation_screen':r})
    return {'raw_cross_problem_reductions':len(rows),'counts':dict(counts),'rows':result,
            'joint_checks':checks,'max_work_per_native_closure':max_work,
            'claim_ceiling':'Recorded-edge screening only; no candidate is a certified useful or novel transfer.'}
