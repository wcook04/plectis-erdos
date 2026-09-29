#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Build the explicitly authored #269 demonstration from the packet's native sources.

This is a fixture builder, not p1's general pre-digestion implementation. All
line spans are resolved from unique source phrases and carry byte digests.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
from short_paper_writer import ROOT, digest, read_json, safe_path, Refusal

PAPER='paper/269/erdos-269-three-prime-running-lcm.tex'
PID='erdos-269-three-prime-running-lcm'
RID='res:distinct-height-all'


def build(root: Path) -> tuple[dict,dict]:
    text=safe_path(root,PAPER).read_text(); lines=text.splitlines(keepends=True)
    def span(first: str,last: str | None=None) -> dict:
        if text.count(first)!=1: raise Refusal('demo.source',f'opening phrase not unique: {first}')
        start=text.index(first)
        end=start+len(first) if last is None else text.index(last,start)+len(last)
        a=text.count('\n',0,start)+1;b=text.count('\n',0,end)+1
        return dict(path=PAPER,start_line=a,end_line=b,sha256=digest(''.join(lines[a-1:b])))
    theorem=re.search(r'\\begin\{theorem\}\[the distinct-height sums\]\\label\{res:distinct-height-all\}\s*(.*?)\\end\{theorem\}',text,re.S)
    if not theorem: raise Refusal('demo.source','canonical theorem absent')
    statement=theorem.group(1).strip()
    native=next(r for r in read_json(root/'docs/paper_lean_coverage.json')['rows'] if r['id']==PID+'#'+RID)
    theorem_span=span('\\begin{theorem}[the distinct-height sums]', '\\end{theorem}')
    abstract_span=span('For every finite set $P$ of at least two primes,','is irrational.')
    proof_span=span('\\begin{proof}[Outline of the proof of Theorem~\\ref{res:distinct-height-all}]','\\end{proof}')
    status_span=span('\\evidenceremark{Ordinary proof, outlined below','which is checked in Lean.}')
    definition_span=span('Let $P$ be a finite set of primes with $|P|\\ge2$','\\mathcal D_P=1+\\sum_{k\\ge1}\\frac1{Q_k}.')
    words_span=span('For an infinite word $u=u_1u_2\\cdots$','\\end{lemma}')
    block_span=span('\\begin{lemma}[rearranged blocks]', '\\end{proof}')
    walls_span=span('\\begin{lemma}[two walls]', 'their arrangement.')
    attribution_span=span('In a letter dated 1 January 1973','letter prints no argument~\\cite{erdos1974letter}.')
    relation_span=span('For a finite prime set $P$, let $\\mathcal S_P$','$\\mathcal D_{\\{2,3,5\\}}$.')
    boundary_span=span('For the repeated $\\{2,3,5\\}$','coprime to $30$ after arbitrarily late starts are unproved.')
    status=(r'Ordinary proof in the companion record, Section~4.1. The source reports a '
            r'second AI-agent check and no human review. This general statement has no Lean proof; '
            r'Comparator does not apply.')
    result=dict(id=RID,statement=statement,
        generality=r'The ordinary argument treats all finite prime sets together. A separate proof for $P=\{2,3,5\}$ is recorded as Lean-checked; that formal support does not extend to the general proof.',
        mechanism_sentence=r'Rationality would force sufficiently close scaled tails to be equal, whereas interchanging two distinct primes changes the integer contribution of their block.',
        hard_step=r'The difficult step is to produce a small return of the prime-crossing orbit that reverses a pair of crossings and leaves an arbitrarily long initial part unchanged. For $|P|\ge4$, the source finds a point on exactly two coordinate walls of the orbit closure and uses nearby returns to isolate this pair.',
        evidence={'class':'ordinary_reviewed','locators':[theorem_span,status_span,proof_span]},
        consumers=[{'paper':PAPER,'label':RID}],
        attribution=r'Erd\H{o}s asserted the distinct-height result in a letter dated 1 January 1973; the letter supplies no proof. The source manuscript gives the ordinary argument used here.',
        open_questions=[r'The repeated-value series for $P=\{2,3,5\}$ remains unresolved in the supplied source.'])
    ext=dict(paper_id=PID,title=r'Irrational Distinct-Height Sums for Finite Prime Sets',
        reader='A number theorist encountering these sums for the first time.',
        lead_result_id=RID,selection_review='authored_selection_not_ranked_by_writer',
        target_relation='related_distinct_target',
        attribution_bibliography={'source':PAPER,'keys':['erdos1974letter']},
        abstract_statement=r'For every finite set $P$ of at least two primes, the sum of the reciprocals of the distinct running least common multiples of the $P$-smooth integers is irrational.',
        motivation=r'Running least common multiples repeat as the smooth integers are enumerated. Counting each distinct value once isolates the series treated by the theorem.',
        definitions=r'Let $P$ be a finite set of at least two primes. An integer is $P$-smooth when all its prime factors lie in $P$. For $t\ge1$, write $H_P(t)=\prod_{p\in P}p^{\lfloor\log_p t\rfloor}$ for the running least common multiple up to $t$. List the prime powers from $P$ as $t_1<t_2<\cdots$ and set $Q_k=H_P(t_k)$. The distinct-height sum is $\mathcal D_P=1+\sum_{k\ge1}Q_k^{-1}$.',
        problem_relation=r'Erd\H{o}s Problem~269 concerns $\mathcal R_P=\sum_{u\in\mathcal S_P}H_P(u)^{-1}$, where $\mathcal S_P$ contains all positive $P$-smooth integers, including $1$. This retains multiplicities. For $P=\{2,3,5\}$, the integers $5$ and $6$ have the same running least common multiple $60$: they contribute $2/60$ to $\mathcal R_P$ and only $1/60$ to $\mathcal D_P$. The theorem concerns $\mathcal D_P$; it does not establish irrationality of $\mathcal R_P$.',
        boundary=r'The repeated-value series in Erd\H{o}s Problem~269 is a different sum; its irrationality for $P=\{2,3,5\}$ is unresolved in the supplied source.',
        proof_outline=r'Each prime power encountered multiplies the running height by its prime. Record those primes as a word. If $\mathcal D_P=N/K$, the tails $x_k=\sum_{j>k}Q_k/Q_j$ satisfy $Kx_k\in\mathbb Z$. A suitable orbit return produces two words with a long common beginning and later blocks that are rearrangements of one another. The common beginning makes the tail difference smaller than $1/K$, so the tails are equal. For a block $\sigma$, write $f(\sigma)$ for the sum of its suffix products. Equal tails and equal block products force these integer contributions to agree, because the remaining suffix values lie in $(0,1)$. For two distinct primes, $f(ab)=1+b$ and $f(ba)=1+a$, which contradict that agreement.',
        long_record_route=r'The full argument is in the companion, Section~4.1, including the two-wall lemma numbered 4.4 there. The short source also gives the integral-tail and rearranged-block lemmas and the proof outline. These passages must remain recoverable when this opening is integrated.',
        lead=dict(hypotheses=r'$P$ is a finite set of primes and $|P|\ge2$.',
                  statement_includes_hypotheses='authored_checked',status_phrase=status,
                  naturalness=r'The assumptions specify the finite-prime family itself; the theorem adds no growth, density, or independence hypothesis on its primes.',
                  review={'kind':'source_reported_ai','performed_by_this_writer':False},
                  native_binding={'id':native['id'],'statement_sha256':native['statement_sha256']}),
        bindings={'abstract_statement':[abstract_span],'statement':[theorem_span],'generality':[theorem_span,status_span],
                  'hypotheses':[theorem_span],'status':[status_span],'naturalness':[theorem_span],
                  'mechanism':[proof_span,block_span],'hard_step':[proof_span,walls_span],
                  'attribution':[attribution_span],'motivation':[relation_span],'definitions':[definition_span],
                  'problem_relation':[relation_span],'boundary':[boundary_span],
                  'proof_outline':[words_span,block_span,proof_span],'long_record_route':[proof_span,walls_span]},
        authored_review={'status':'source-grounded editorial construction; semantic admission required',
                         'new_theorem_claims':False,'reviewed_whole_proof':False,
                         'note':'The theorem is copied in the native presentation normal form; the other roles paraphrase cited source spans.'})
    dossier={'schema':'dossier/1','problem':269,'results':[result],
             'landscape':{'routes':[],'failed_routes_with_scope':[],'generalisations':[]},
             'sources':[theorem_span,proof_span,relation_span],
             'extensions':{'short_paper_v1':ext}}
    evidence={'schema':'claim_evidence/1','rows':[dict(paper_id=PID,claim_locator=RID,
              statement_hash=digest(statement),evidence_class='ordinary_reviewed',lean_declaration=None,
              comparator_receipt=None,ordinary_proof_locator=proof_span,status_phrase_required=status)]}
    return dossier,evidence


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=ROOT);p.add_argument('--output-dir',type=Path,required=True)
    args=p.parse_args();d,e=build(args.root);args.output_dir.mkdir(parents=True,exist_ok=True)
    for name,obj in [('dossier269.json',d),('claim_evidence269.json',e)]:
        (args.output_dir/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
    print('wrote authored corpus-derived fixture; no p1 or p2 return was available')
if __name__=='__main__':main()
