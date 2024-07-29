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

(** We would like to also enforce security for arbitrary programs that are do
    not follow the cryptographic constant time programming discipline
    (i.e. which do not satisfy [ct_well_typed]). The goal is to achieve a
    relative notion of security which intuitively ensures that the protected
    program does not leak more information speculatively than the original
    program leaks sequentially via the CT observations. One way to achieve this
    protection is by transforming the program using standard Speculative Load
    Hardening (SLH), instead of the selective variant from the previous chapter. *)

(** We formalize this as a relative security property that doesn't label data at
    all as public or secret. This seems to roughly correspond to the "weak
    speculative non-interference" from the paper "Hardware-Software Contracts
    for Secure Speculation" (IEEE SP 2021). *)

Definition seq_obs_secure c st1 st2 :Prop :=
  forall ast1 ast2 stt1 stt2 astt1 astt2 os1 os2,
    <(st1, ast1)> =[ c ]=> <(stt1, astt1, os1)> ->
    <(st2, ast2)> =[ c ]=> <(stt2, astt2, os2)> ->
    os1 = os2.

Definition spec_obs_secure c st1 st2 :Prop :=
  forall ds ast1 ast2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure (trans : com -> com) (c:com) (st1 st2:state) : Prop :=
  seq_obs_secure c st1 st2  -> 
  spec_obs_secure (trans c) st1 st2.  

(** * Standard Speculative Load Hardening (SLH, not selective *)

Definition AllPub : pub_vars := (_!-> true).

Definition slh := sel_slh AllPub.

Definition ideal_eval_slh := ideal_eval AllPub.

(* We can reuse the BCC proof for proving [relative_secure slh] *)

Lemma slh_bcc : forall c ds st ast (b: bool) st' ast' b' os,
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <(st, ast, b, ds)> =[ slh c ]=> <(st', ast', b', os)> ->
  AllPub |- <(st, ast, b, ds)> =[ c ]=> <("b" !-> st "b"; st', ast', b', os)>.
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
  forall c st1 st2,
    (* some extra assumptions needed by slh_bcc *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    relative_secure slh c st1 st2.
Proof.
  unfold relative_secure, seq_obs_secure, spec_obs_secure.
  intros c st1 st2 Hunused Hst1b Hst2b Hseq ds ast1 ast2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 Hev1 Hev2.
  apply slh_bcc in Hev1; try assumption.
  apply slh_bcc in Hev2; try assumption.
  eapply same_final_b in Hev1 as SameB; try eassumption. subst.
  destruct bt1 eqn:Eqbt1.
  - (* with speculation *)
    destruct c as [| X e | c1 c2 | be ct cf | be cw | X a ie | a ie e ] eqn:Eqnc;
    inversion Hev1; subst; clear Hev1; inversion Hev2; subst; clear Hev2;
    simpl in *; eauto.
    + (* Ideal_Seq *) admit.
    + (* Ideal_If *) admit.
    + (* Ideal If_F *) admit.
    + (* Ideal_While *) admit.
  - (* without speculation *)
    pose proof (ideal_eval_no_spec _ _ _ _ _ _ _ _ Hev1) as NoSpec.
    eapply ideal_eval_no_spec_to_seq in Hev1; try assumption.
    eapply ideal_eval_no_spec_to_seq in Hev2; try assumption.
    eauto.
Admitted.

Fixpoint sub_com (c1 c2 :com) :Prop :=
  match c2 with 
  | <{{ c21; c22 }}> => c1 = c2 \/ sub_com c1 c21 \/ sub_com c1 c22
  | <{{ if be2 then ct2 else cf2 end }}> =>
        c1 = c2 \/ sub_com c1 ct2 \/ sub_com c1 cf2
  | <{{ while be2 do cw2 end }}> => c1 = c2 \/ sub_com c1 cw2
  | _ => c1 = c2
  end.

Lemma sub_com_refl : forall c, sub_com c c.
Proof. destruct c; simpl; auto. Qed.

Lemma sub_com_seq_obs_secure : forall c1 c2 st1 st2,
  spec_obs_secure c2 st1 st2 ->
  sub_com c1 c2 ->
  spec_obs_secure c1 st1 st2.
Proof.
Admitted.

Fixpoint branching_on_bexp (be :bexp) (c :com) :Prop :=
  match c with
  | <{{ c1; c2 }}> =>  branching_on_bexp be c1 \/ branching_on_bexp be c2
  | <{{ if be' then ct else cf end }}> => 
        be = be' \/ branching_on_bexp be ct \/ branching_on_bexp be cf
  | <{{ while be' do cw end }}> => be = be' \/ branching_on_bexp be cw
  | _  => False
  end.

Definition branch_equiv (c :com) (st1 st2 :state) :Prop :=
  forall be, branching_on_bexp be c -> beval st1 be = beval st2 be.

Lemma branch_equiv_seq_obs_secure : forall c st1 st2,
  branch_equiv c st1 st2 ->
  seq_obs_secure c st1 st2.
Admitted.