(** * FlexSLH: Selective Ultimate SLH *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From SECF Require Import SpecCT.
From SECF Require Import UltimateSLH.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

Fixpoint label_of_aexp (P:pub_vars) (a:aexp) : label :=
  match a with
  | ANum n => public
  | AId X => P X
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ be ? a1 : a2 }> => join (label_of_bexp P be)
                            (join (label_of_aexp P a1) (label_of_aexp P a2))
  end
with label_of_bexp (P:pub_vars) (a:bexp) : label :=
  match a with
  | <{ true }> | <{ false }> => public
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ ~b }> => label_of_bexp P b
  | <{ b1 && b2 }> => join (label_of_bexp P b1) (label_of_bexp P b2)
  end.

Fixpoint flex_slh (P:pub_vars) (c:com) : com :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ flex_slh P c1; flex_slh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      if label_of_bexp P be
      then (* Selective SLH *)
        <{{if be then "b" := be ? "b" : 1; flex_slh P c1
                 else "b" := be ? 1 : "b"; flex_slh P c2 end}}>
      else (* Ultimate SLH *)
        <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; flex_slh P c1
                            else "b" := ("b" = 0 && be) ? 1 : "b"; flex_slh P c2 end}}>
  | <{{while be do c end}}> =>
      if label_of_bexp P be
      then (* Selective SLH *)
        <{{while be do "b" := be ? "b" : 1; flex_slh P c end;
           "b" := be ? 1 : "b"}}>
      else (* Ultimate SLH *)
        <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; flex_slh P c end;
           "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    if label_of_aexp P i
    then (* Selective SLH *)
      if P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
             else <{{x <- a[[i]]}}>
    else (* Ultimate SLH *)
      <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> =>
    if label_of_aexp P i
    then (* Selective SLH *)
      <{{a[i] <- e}}> (* <- Doing nothing here okay for Spectre v1,
         but problematic for return address or code pointer overwrites *)
    else (* Ultimate SLH *)
      <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

(* Unclear if the following type system that just tracks explicit and implicit
   flows is good enough for what we need. *)

Reserved Notation "P '&' PA ',' pc '|--' c" (at level 40).

Inductive well_typed (P PA : pub_vars) : label -> com -> Prop :=
  | WT_Com : forall pc,
      P & PA, pc |-- <{ skip }>
  | WT_Asgn : forall pc X a l,
      P |-a- a \in l ->
      can_flow (join pc l) (P X) = true ->
      P & PA, pc |-- <{ X := a }>
  | WT_Seq : forall pc c1 c2,
      P & PA, pc |-- c1 ->
      P & PA, pc |-- c2 ->
      P & PA, pc |-- <{ c1 ; c2 }>
  | WT_If : forall pc b l c1 c2,
      P |-b- b \in l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, (join pc l) |-- c2 ->
      P & PA, pc |-- <{ if b then c1 else c2 end }>
  | WT_While : forall pc b l c1,
      P |-b- b \in l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, pc |-- <{ while b do c1 end }>
  | WT_ARead : forall pc x a i li,
      P |-a- i \in li ->
      can_flow (join li (PA a)) (P x) = true ->
      P & PA, pc |-- <{{ x <- a[[i]] }}>
  | WT_AWrite : forall pc a i e li l,
      P |-a- i \in li ->
      P |-a- e \in l ->
      can_flow (join li l) (PA a) = true ->
      P & PA, pc |-- <{{ a[i] <- e }}>
where "P '&' PA ',' pc '|--' c" := (well_typed P PA pc c).

Conjecture flex_slh_relative_secure :
  forall P PA c st1 st2 ast1 ast2,
    (* Selective SLH assumptions *)
    P & PA, public |-- c -> (* just that this is weaker (not ct_well_typed) *)
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    (* Joint assumptions *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    (* Ultimate SLH assumptions  *)
    nonempty_arrs ast1 ->
    nonempty_arrs ast2 ->
    relative_secure (flex_slh P) c st1 st2 ast1 ast2.
