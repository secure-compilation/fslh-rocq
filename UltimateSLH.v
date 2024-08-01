(** * UltimateSLH: Relative Security Against Speculation Attacks*)

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
    protection is by transforming the program using Ultimate Speculative Load
    Hardening (USLH), instead of the selective variant from the previous chapter. *)

(** We formalize this as a relative security property that doesn't label data at
    all as public or secret. *)

Definition seq_obs_secure c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2,
    <(st1, ast1)> =[ c ]=> <(stt1, astt1, os1)> ->
    <(st2, ast2)> =[ c ]=> <(stt2, astt2, os2)> ->
    os1 = os2.

Definition spec_obs_secure c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure (trans : com -> com) (c:com) (st1 st2:state) : Prop :=
  forall ast1 ast2,
    seq_obs_secure c st1 st2 ast1 ast2 ->
    spec_obs_secure (trans c) st1 st2 ast1 ast2.

(** * Ultimate Speculative Load Hardening *)

(* HIDE: With BOr cand do [be || "b" <> 0], but whatever can also do it with BAnd
Definition BOr b1 b2 := BNot (BAnd (BNot b1) (BNot b2)).
Notation "x || y"  := (BOr x y) (in custom com at level 80, left associativity). *)

Axiom MASK : nat.

Fixpoint ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ ultimate_slh c1; ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if be && "b" = 0 then "b" := (be ? "b" : 1); ultimate_slh c1
                          else "b" := (be ? 1 : "b"); ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while be && "b" = 0 do "b" := (be ? "b" : 1); ultimate_slh c end;
         "b" := (be ? 1 : "b")}}>
  | <{{x <- a[[i]]}}> =>
    <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

Fixpoint observations (c:com) (ds:dirs) : obs :=
  match c with
  | <{{skip}}> => []
  | <{{x := e}}> => []
  | <{{c1; c2}}> => observations c2 ds ++ observations c1 ds
  | <{{if be then c1 else c2 end}}> => observations c2 ds ++ [OBranch false]
  | <{{while be do c end}}> => []
  | <{{x <- a[[i]]}}> => [OARead a 0]
  | <{{a[i] <- e}}> => [OAWrite a 0]
  end.

Lemma observations_fixed : forall c st ast ds stt astt os,
  unused "b" c ->
  st "b" = 1 ->
  <(st, ast, true, ds)> =[ ultimate_slh c ]=> <(stt, astt, true, os)> ->
  os = observations c ds.
Admitted.

Lemma gilles_lemma : forall c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2,
  unused "b" c ->
  st1 "b" = 1 ->
  st2 "b" = 1 ->
  <(st1, ast1, true, ds)> =[ ultimate_slh c ]=> <(stt1, astt1, true, os1)> ->
  <(st2, ast2, true, ds)> =[ ultimate_slh c ]=> <(stt2, astt2, true, os2)> ->
  os1 = os2.
Proof.
  intros c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2 Hunused Hb1 Hb2 H1 H2.
  apply observations_fixed in H1; try auto.
  apply observations_fixed in H2; try auto. congruence.
Qed.

(* TODO: this should be defined wrt a new ideal semantics for Ultimate SLH *)
Definition ideal_spec_obs_secure c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Lemma relative_noninterference : forall c st1 st2 ast1 ast2,
  unused "b" c ->
  st1 "b" = 1 ->
  st2 "b" = 1 ->
  seq_obs_secure c st1 st2 ast1 ast2 ->
  ideal_spec_obs_secure c st1 st2 ast1 ast2.
Admitted.

Theorem relative_secure_slh :
  forall c st1 st2,
    (* some extra assumptions needed by slh_bcc *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    relative_secure ultimate_slh c st1 st2.
Admitted. (* from relative noninterference + bcc *)
