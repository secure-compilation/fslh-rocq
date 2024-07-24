(** * SpecRelative: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From SECF Require Import SpecCT.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(** * Relative security *)

Definition relative_secure (trans : com -> com) (c:com) (s1 s2:state) : Prop :=
  forall as1 as2,
   (* original program c sequentially secure for some initial states *)
   (forall s1' s2' as1' as2' os1 os2,
      <(s1, as1)> =[ c ]=> <(s1', as1', os1)> ->
      <(s2, as2)> =[ c ]=> <(s2', as2', os2)> ->
      os1 = os2) ->
  (* transformed program speculatively secure these initial states *)
  (forall ds s1' s2' as1' as2' os1 os2 b1' b2',
    <(s1, as1, false, ds)> =[ trans c ]=> <(s1', as1', b1', os1)> ->
    <(s2, as2, false, ds)> =[ trans c ]=> <(s2', as2', b2', os2)> ->
    os1 = os2).

(** * Speculative Load Hardening (SLH, not selective *)

Definition AllP : pub_vars := fun X => true.

Definition slh := sel_slh AllP.

Definition ideal_eval_slh := ideal_eval AllP.

(* We can reuse the BCC proof for proving [relative_secure slh] *)

Lemma slh_bcc : forall c ds st ast (b: bool) st' ast' b' os,
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <(st, ast, b, ds)> =[ slh c ]=> <(st', ast', b', os)> ->
    AllP |- <(st, ast, b, ds)> =[ c ]=> <("b" !-> st "b"; st', ast', b', os)>.
Proof. intros; eapply sel_slh_ideal; eauto. Qed.

Conjecture same_final_b : forall P c s1 s2 as1 as2 b ds s1' s2' as1' as2' b1' b2' os1 os2,
  P |- <( s1, as1, b, ds )> =[ c ]=> <( s1', as1', b1', os1 )> ->
  P |- <( s2, as2, b, ds )> =[ c ]=> <( s2', as2', b2', os2 )> ->
  b1' = b2'.

Conjecture ideal_eval_no_spec : forall P c s ast ds s' ast' os,
  P |- <( s, ast, false, ds )> =[ c ]=> <( s', ast', false, os )> ->
  (forall d, In d ds -> d = DStep).

Conjecture ideal_eval_no_spec_to_seq : forall P c s ast ds s' ast' os,
  (forall d, In d ds -> d = DStep) ->
  P |- <( s, ast, false, ds )> =[ c ]=> <( s', ast', false, os )> ->
  <( s, ast )> =[ c ]=> <( s', ast', os )>.

Theorem relative_secure_slh :
  forall c s1 s2,
    (* some extra assumptions needed by slh_bcc *)
    unused "b" c ->
    s1 "b" = 0 ->
    s2 "b" = 0 ->
    relative_secure slh c s1 s2.
Proof.
  unfold relative_secure.
  intros c s1 s2 Hunused Hb1 Hb2 as1 as2 H ds s1' s2' as1' as2' os1 os2 b1' b2' H1 H2.
  apply slh_bcc in H1; try assumption.
  apply slh_bcc in H2; try assumption.
  eapply same_final_b in H1 as SameB; try eassumption. subst.
  destruct b1' eqn:Eqb1'.
  - (* with speculation *) admit. (* ... the difficult case ... *)
  - (* without speculation *)
    pose proof (ideal_eval_no_spec _ _ _ _ _ _ _ _ H1) as NoSpec.
    eapply ideal_eval_no_spec_to_seq in H1; try assumption.
    eapply ideal_eval_no_spec_to_seq in H2; try assumption.
    eauto.
Admitted.
