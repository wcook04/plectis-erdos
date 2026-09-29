Erdős #251 | source-bound frontier
Snapshot: sha256:dd6c9fa13a7010924a0de2e161509b881d36d017e9ab225fcb887f0804e3254b

Generated navigation over pinned owner bytes, not a new mathematical authority. Status strings are owner-reported, compilation is not replayed here, dependencies are not implications, and unbound relation text is excluded from inference.

Programme statement (verbatim, not a claim of unique maximal strength):
Lean proves that Π = ∑_{n≥1} p_n/2ⁿ equals 2 plus the prime-gap dyadic series and that Π is irrational if and only if that gap series is (tsum_primeDyadicTerm_eq_two_add_primeGap_unconditional, irrational_tsum_primeDyadicTerm_iff_primeGap), with summability from the elementary bound p_n ≤ 1250(n+1)^4; the identity is the known summation by parts. Lean also proves that the consecutive prime gaps are unbounded and not eventually periodic (exists_primeGap0_gt, primeGap0_not_eventually_periodic). The irrationality of Π remains open: these facts do not supply the required cofinal escape for the actual prime gaps.

Registered open obligations:
- remaining_open.erdos_251_irrationality: Prove that Π = ∑_{n≥1} p_n/2ⁿ is irrational; the exact tail-shift equivalence and prime-gap constraints do not supply the required cofinal escape.

Results explicitly named by the programme statement (not paginated):
- prime_gap_irrationality_equivalence [formalised here]: Lean checks that the prime-value dyadic series is irrational exactly when the prime-gap dyadic series is. The named iff still takes a Summable hypothesis; this checkout discharges that hypothesis by the elementary bound p_n ≤ 1250(n+1)^4 (not the prime-number theorem) and the unconditional identity. Neither side is proved irrational. This formalises known summation-by-parts; the public attribution of that identity is the cited-only row prime_gap_identity_tao.
- prime_gap_unboundedness_and_nonperiodicity [unconditional progress]: The consecutive-prime-gap sequence is unbounded and is not eventually periodic with any positive period. These coefficient facts do not by themselves imply irrationality of the prime-gap or prime-index dyadic series.

Endpoint certificate signatures (source-listed; typed replay required):

Registered results (identifier order, never strength order):
- prime_gap_irrationality_equivalence [formalised here]: Lean checks that the prime-value dyadic series is irrational exactly when the prime-gap dyadic series is. The named iff still takes a Summable hypothesis; this checkout discharges that hypothesis by the elementary bound p_n ≤ 1250(n+1)^4 (not the prime-number theorem) and the unconditional identity. Neither side is proved irrational. This formalises known summation-by-parts; the public attribution of that identity is the cited-only row prime_gap_identity_tao.
- prime_gap_unboundedness_and_nonperiodicity [unconditional progress]: The consecutive-prime-gap sequence is unbounded and is not eventually periodic with any positive period. These coefficient facts do not by themselves imply irrationality of the prime-gap or prime-index dyadic series.

Known misreadings:
- c-251-equivalence-no-supply: The theorem shows the prime dyadic series and the prime-gap dyadic series are irrational together, given summability of the prime dyadic series, which the corpus proves (summable_primeDyadicTerm). Both irrationality statements stay open. Credit counts them as one question, and search may keep both views.

Relations: 1 navigation rows; existing endpoint text is quarantined.
Recorded attempts: 10; paper-ledger rows: 45.
Use JSON for complete source references, relation observations and attempt boundaries.
Current argument graph: not_admitted_no_current_replay_receipt
Page: {"next":null,"offset":0,"order":"identifier_not_strength","returned":2,"total":2}
