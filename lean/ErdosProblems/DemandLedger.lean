/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.DemandLedger.Basic
import ErdosProblems.DemandLedger.edges.ClusterA
import ErdosProblems.DemandLedger.edges.ClusterB
import ErdosProblems.DemandLedger.edges.ClusterC
import ErdosProblems.DemandLedger.edges.ClusterD
import ErdosProblems.DemandLedger.edges.ClusterE
import ErdosProblems.DemandLedger.edges.ClusterF
import ErdosProblems.DemandLedger.edges.Bridge1
import ErdosProblems.DemandLedger.edges.Bridge2
import ErdosProblems.DemandLedger.edges.Bridge3
import ErdosProblems.DemandLedger.edges.Discharge1_G097
import ErdosProblems.DemandLedger.edges.Discharge2_G100
import ErdosProblems.DemandLedger.edges.Discharge3_G103

/-!
# Checked antecedent relations retained from an earlier extraction

This namespace preserves exact propositions extracted from named theorem
binders with `hypOf%` and the implications that were proved between them. It is
a checked mathematical artifact, not the live statement census, candidate
ranking or agent restatement service for the current public corpus.

Current agents discover reviewed claims with `scripts/query_corpus.py`, navigate
current statement families with `scripts/query_semantic.py`, and compare one
proposed reduction with its target using `scripts/residual_evaluator.py`.
Specific equivalences in this namespace remain valid at their theorem types;
an absent edge remains unproved rather than refuted.
-/
