# FSLH: Flexible Mechanized Speculative Load Hardening

This artifact contains a complete Rocq formalization of the following paper:

- [FSLH: Flexible Mechanized Speculative Load Hardening](https://arxiv.org/abs/2502.03203).
  Jonathan Baumann, Roberto Blanco, Léon Ducruet, Sebastian Harwig, and Catalin Hritcu.
  In 35th IEEE Computer Security Foundations Symposium (CSF). June 2025.

The latest version of this artifact is available at:
https://github.com/secure-compilation/fslh-rocq

## Requirements

The development uses the [Rocq prover](https://rocq-prover.org).

We tested this with versions 8.19.2, 8.20.0 and 8.20.1, when it was still called Coq.

Installation instructions for these versions are available here:
https://web.archive.org/web/20250305221757/https://coq.inria.fr/download

From OPAM just run:

    $ opam install coq.8.20.1

## Building

For having Rocq check our proofs run `make` in the root directory of the development.

## Key results

Theorem 1 (SaSLH is SCT-secure). File `FlexSLH.v`, Theorem `addr_sel_slh_spec_ct_secure`

Theorem 2 (USLH is relative-secure). File `FlexSLH.v`, Theorem `ultimate_slh_relative_secure`

Theorem 3 (FaSLH is relative-secure). File `FlexSLH.v`, Theorem `flex_aslh_relative_secure`

Theorem 4 (Connection between FaSLH and SaSLH). File `FlexSLH.v`, Lemma `addr_sel_slh_is_flex_aslh`

Theorem 5 (Connection between FaSLH and USLH). File `FlexSLH.v`, Lemma `ultimate_slh_is_flex_aslh`

Theorem 6 (FvSLH∀ is relative-secure). File `FlowSensitiveFSLH.v`, Lemma `fs_flex_vslh_relative_secure` 

Theorem 7 (FvSLH is relative-secure). File `FlexVSLH.v`, Theorem `flex_vslh_relative_secure`

Theorem 8 (SvSLH is SCT-secure). File `FlexVSLH.v`, Theorem `val_sel_slh_spec_ct_secure`

<!--Theorem 8 (Connection between FvSLH and SvSLH). File `FlexVSLH.v`, Lemma `val_sel_slh_is_flex_vslh`-->
<!---->
<!--Theorem 9 (Connection between FvSLH and USLH). File `FlexVSLH.v`, Lemma `ultimate_slh_is_flex_vslh`-->
<!---->
Lemma 1 (Backwards compiler correctness). File `FlexSLH.v`, Lemma `flex_aslh_bcc_generalized`

Lemma 2 (Noninterference in the ideal semantics for iSLH with equal observations).
File `FlexSLH.v`, Lemma `ideal_eval_small_step_noninterference`

Lemma 3 (Unwinding of ideal misspeculated executions). File `FlexSLH.v`, Lemma `ideal_misspeculated_unwinding`

Lemma 4 (Ideal semantics is relative-secure). File `FlexSLH.v`, Lemma `ideal_eval_relative_secure`

<!--Lemma 5 (Noninterference in the ideal semantics for vSLH).-->
<!--File `FlexVSLH.v`, Lemma `ideal_eval_small_step_noninterference`-->
Lemma 5 (Backwards compiler correctness for FvSLH∀). File `FlowSensitiveFSLH.v`, Lemma `flex_slh_acom_bcc_generalized`

Lemma 6 (IFC analysis produces well-labeled programs). File `FlowSensitiveFSLH.v`, Lemma `static_tracking_well_labeled`

Lemma 7 (Ideal semantics preserves well-labeledness). File `FlowSensitiveFSLH.v`, Lemma `ideal_eval_preserves_well_labeled`

Lemma 8 (Ideal semantics ensures relative security). File `FlowSensitiveFSLH.v`, Lemma `ideal_eval_relative_secure`

## Assumptions

Use `Print Assumptions` to check that the above theorems are all fully proved:
https://coq.inria.fr/doc/V8.20.0/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions

The proofs only assume functional extensionality, decidability of map lookups,
and exercises from the Maps library of Software Foundations textbook for which
we didn't want to publicly leak the solutions.

## Testing experiments

The testing experiments in the `testing` sub-directory additionally depend on
the [QuickChick](https://github.com/QuickChick/QuickChick) library.
We tested with version 2.0.5. These testing experiments informed the design of
FSLH, but are not part of the final artifact, which only includes full proofs.
