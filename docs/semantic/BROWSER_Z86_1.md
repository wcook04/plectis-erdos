# Z86_1: Erdős 257 selected windows: exact one-bit extension and dependent-index coherence

[All problems and zones](BROWSER.md)

<a id="node-351bcd00973905d5"></a>
## equal_selected_indices_determine_the_same_word_independently_of_bound_proofs

PROVED DEPENDENT-INDEX COHERENCE: in a SelectedHalfWindow, if two carry indices k and ℓ are equal, then the selected words are equal regardless of which proofs witness their positivity and window bounds.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem identifies only words already selected at the same index. It asserts neither uniqueness among all admissible words nor agreement between different carry indices.

- Lean declaration: [SelectedHalfWindow.word_eq_of_index_eq](../../Erdos249257/HalfCarrySelectedWindow.lean#L617)

- outgoing **complements**: [Z86::one_bit_extension_preserves_the_parent_and_has_an_exact_support_normal_form](BROWSER_Z86_1.md#node-03b4919ac27d91fe). The index-coherence lemma erases dependent proof choices when extension and restriction identities are composed across selected-window history steps.

<a id="node-03b4919ac27d91fe"></a>
## one_bit_extension_preserves_the_parent_and_has_an_exact_support_normal_form

PROVED EXTENSION PACKET: extending a half word by a Boolean bit agrees with the parent at every cast-successor index and equals the appended bit at the final index. Membership in its support is exactly old support membership or the new terminal index with bit true; therefore its support is unchanged for false and gains precisely N+1 for true, and restricting the extension recovers the parent word.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The packet only describes a supplied extension. It does not show that the child satisfies a carry target, remains strip-admissible, or belongs to a coherent protected family.

- Lean declaration: [extendHalfWord_castSucc](../../Erdos249257/HalfCarrySelectedWindow.lean#L68)
- Lean declaration: [extendHalfWord_last](../../Erdos249257/HalfCarrySelectedWindow.lean#L73)
- Lean declaration: [mem_wordSupport_extendHalfWord_iff](../../Erdos249257/HalfCarrySelectedWindow.lean#L80)
- Lean declaration: [wordSupport_extendHalfWord](../../Erdos249257/HalfCarrySelectedWindow.lean#L118)
- Lean declaration: [restrictWord_extendHalfWord](../../Erdos249257/HalfCarrySelectedWindow.lean#L127)

- incoming **complements**: [Z86::equal_selected_indices_determine_the_same_word_independently_of_bound_proofs](BROWSER_Z86_1.md#node-351bcd00973905d5). The index-coherence lemma erases dependent proof choices when extension and restriction identities are composed across selected-window history steps.

