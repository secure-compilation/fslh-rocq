# Requirements

The development uses the Rocq proof assistant (formerly known as Coq)

Installation instructions: https://coq.inria.fr/download

Tested with versions 8.19.2, 8.20.0 and 8.20.1

# Building

Run `make` to build the development

# Key results

Theorem 1 (SaSLH is CCT-secure). File `FlexSLH.v`, Theorem `addr_sel_slh_spec_ct_secure`

Theorem 2 (USLH is relative-secure). File `FlexSLH.v`, Theorem `ultimate_slh_relative_secure`

Theorem 3 (FaSLH is relative-secure). File `FlexSLH.v`, Theorem `flex_aslh_relative_secure`

Theorem 4 (Connection between FaSLH and SaSLH). File `FlexSLH.v`, Lemma `addr_sel_slh_is_flex_aslh`

Theorem 5 (Connection between FaSLH and USLH). File `FlexSLH.v`, Lemma `ultimate_slh_is_flex_aslh`

Theorem 6 (Connection between FvSLH and SvSLH). File `FlexVSLH.v`, Lemma `val_sel_slh_is_flex_vslh`

Theorem 7 (Connection between FvSLH and USLH). File `FlexVSLH.v`, Lemma `ultimate_slh_is_flex_vslh`

Theorem 8 (FvSLH is relative-secure). File `FlexVSLH.v`, Theorem `flex_vslh_relative_secure`

Theorem 9 (SvSLH is CCT-secure). File `FlexVSLH.v`, Theorem `val_sel_slh_spec_ct_secure`

Lemma 1 (Backwards compiler correctness). File `FlexSLH.v`, Lemma `flex_aslh_bcc_generalized`

Lemma 2 (Ideal unwinding lemma). File `FlexSLH.v`, Lemma `ideal_misspeculated_unwinding`

Lemma 3 (Ideal semantics is relative-secure). File `FlexSLH.v`, Lemma `ideal_eval_relative_secure`

# Assumptions

Use `Print Assumptions` to check that the above theorems are all fully proved

https://coq.inria.fr/doc/V8.20.0/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions

The proofs only assume functional extensionality and decidability of map lookups
