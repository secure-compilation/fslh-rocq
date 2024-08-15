(** * FlexSLH: Selective Ultimate SLH *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From SECF Require Import TestingSpecCT.
(* From SECF Require Import UltimateSLH. *)
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
  | AId X => apply P X
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
      if apply P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
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
      P |-a- a \IN l ->
      can_flow (join pc l) (apply P X) = true ->
      P & PA, pc |-- <{ X := a }>
  | WT_Seq : forall pc c1 c2,
      P & PA, pc |-- c1 ->
      P & PA, pc |-- c2 ->
      P & PA, pc |-- <{ c1 ; c2 }>
  | WT_If : forall pc b l c1 c2,
      P |-b- b \IN l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, (join pc l) |-- c2 ->
      P & PA, pc |-- <{ if b then c1 else c2 end }>
  | WT_While : forall pc b l c1,
      P |-b- b \IN l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, pc |-- <{ while b do c1 end }>
  | WT_ARead : forall pc x a i li,
      P |-a- i \IN li ->
      can_flow (join pc (join li (apply PA a))) (apply P x) = true ->
      P & PA, pc |-- <{{ x <- a[[i]] }}>
  | WT_AWrite : forall pc a i e li l,
      P |-a- i \IN li ->
      P |-a- e \IN l ->
      can_flow (join pc (join li l)) (apply PA a) = true ->
      P & PA, pc |-- <{{ a[i] <- e }}>
where "P '&' PA ',' pc '|--' c" := (well_typed P PA pc c).

Definition nonempty_arrs (ast :astate) :Prop :=
  forall a, 0 < length (apply ast a).

Definition seq_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2,
    <(st1, ast1)> =[ c ]=> <(stt1, astt1, os1)> ->
    <(st2, ast2)> =[ c ]=> <(stt2, astt2, os2)> ->
    os1 = os2.

Definition spec_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure (trans : com -> com) (c:com) (st1 st2 :state) (ast1 ast2 :astate): Prop :=
  seq_same_obs c st1 st2 ast1 ast2 ->
  spec_same_obs (trans c) st1 st2 ast1 ast2.

Conjecture flex_slh_relative_secure :
  forall P PA c st1 st2 ast1 ast2,
    (* Selective SLH assumptions *)
    P & PA, public |-- c -> (* just that this is weaker (not ct_well_typed) *)
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    (* Joint assumptions *)
    unused "b" c ->
    apply st1 "b" = 0 ->
    apply st2 "b" = 0 ->
    (* Ultimate SLH assumptions  *)
    nonempty_arrs ast1 ->
    nonempty_arrs ast2 ->
    relative_secure (flex_slh P) c st1 st2 ast1 ast2.

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import String.

Notation label := TestingSpecCT.label.
Notation apply := TestingSpecCT.apply.
Notation join := TestingSpecCT.join.

Fixpoint wt_typechecker (P PA:pub_vars) (pc:label) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (join pc (label_of_aexp P a)) (apply P X)
  | <{ c1 ; c2 }> => wt_typechecker P PA pc c1 && wt_typechecker P PA pc c2
  | <{ if b then c1 else c2 end }> =>
      wt_typechecker P PA (join pc (label_of_bexp P b)) c1 &&
      wt_typechecker P PA (join pc (label_of_bexp P b)) c2
  | <{ while b do c1 end }> =>
      wt_typechecker P PA (join pc (label_of_bexp P b)) c1
  | <{{ x <- a[[i]] }}> =>
      can_flow (join pc (join (label_of_aexp P i) (apply PA a))) (apply P x)
  | <{{ a[i] <- e }}> =>
      can_flow (join pc (join (label_of_aexp P i) (label_of_aexp P e))) (apply PA a)
  end.

Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Definition gen_pub_aexp_leaf (P : pub_vars) : G aexp :=
  oneOf (liftM ANum arbitrary ;;;
         (let pubs := map Var (filter (apply P) (map_dom (snd P))) in
         if seq.nilp pubs then []
         else [liftM AId (elems_ (Var "X0"%string) pubs)] ) ).

Fixpoint gen_pub_aexp (sz:nat) (P:pub_vars) : G aexp :=
  match sz with
  | O => thunkGen (fun _ => gen_pub_aexp_leaf P)
  | S sz' =>
      freq [ (3, thunkGen (fun _ => gen_pub_aexp_leaf P));
             (sz, thunkGen (fun _ => liftM2 APlus (gen_pub_aexp sz' P) (gen_pub_aexp sz' P)));
             (sz, thunkGen (fun _ => liftM2 AMinus (gen_pub_aexp sz' P) (gen_pub_aexp sz' P)));
             (sz, thunkGen (fun _ => liftM2 AMult (gen_pub_aexp sz' P) (gen_pub_aexp sz' P)))]
  end.

Definition gen_secure_asgn (P:pub_vars) : G com :=
  let vars := map_dom (snd P) in
  x <- elems_ "X0"%string vars;;
  e <- (if apply P x then gen_pub_aexp 1 P else arbitrarySized 1);;
  ret <{ x := e }>.

Definition gen_name (P:pub_vars) (label:bool) : G (option string) :=
  let privs := filter (fun x => Bool.eqb label (apply P x))
                      (map_dom (snd P)) in
  match privs with
  | x0 :: _ => liftM Some (elems_ x0 privs)
  | [] => ret None
  end.

Definition gen_asgn_in_ctx (gen_asgn : pub_vars -> G com)
    (pc:label) (P:pub_vars) : G com :=
  if pc then gen_asgn P
  else
    x <- gen_name P secret;; (* secret var *)
    match x with
    | Some x =>
      e <- arbitrarySized 1;;
      ret <{ x := e }>
    | None => ret <{ skip }>
    end.

Definition gen_secure_aread (P:pub_vars) (PA:pub_arrs) : G com :=
  let vars := map_dom (snd P) in
  x <- elems_ "X0"%string vars;;
  if apply P x then
    a <- gen_name PA public;; (* public array *)
    match a with
    | Some a =>
        i <- gen_pub_aexp 1 P;; (* public index *)
        ret <{ x <- a[[i]] }>
    | None => ret <{ skip }>
    end
  else
    a <- arbitrary;;
    i <- arbitrarySized 1;;
    ret <{ x <- a[[i]] }>.

Definition gen_aread_in_ctx (gen_aread : pub_vars -> pub_arrs -> G com)
    (pc:label) (P:pub_vars) (PA:pub_arrs) : G com :=
  if pc then gen_aread P PA
  else
    x <- gen_name P secret;; (* secret var *)
    match x with
    | Some x =>
      a <- arbitrary;;
      i <- arbitrarySized 1;;
      ret <{ x <- a[[i]] }>
    | None => ret <{ skip }>
    end.

Definition gen_secure_awrite (P:pub_vars) (PA:pub_arrs) : G com :=
  let arrs := map_dom (snd PA) in
  a <- elems_ "A0"%string arrs;;
  if apply PA a then
    i <- gen_pub_aexp 1 P;; (* public index *)
    e <- gen_pub_aexp 1 P;; (* public expression *)
    ret <{ a[i] <- e }>
  else
    i <- arbitrarySized 1;;
    e <- arbitrarySized 1;;
    ret <{ a[i] <- e }>.

Definition gen_awrite_in_ctx (gen_awrite : pub_vars -> pub_arrs -> G com)
    (pc:label) (P:pub_vars) (PA:pub_arrs) : G com :=
  if pc then gen_awrite P PA
  else
    a <- gen_name PA secret;; (* secret array *)
    match a with
    | Some a =>
      i <- arbitrarySized 1;;
      e <- arbitrarySized 1;;
      ret <{ a[i] <- e }>
    | None => ret <{ skip }>
    end.

Fixpoint gen_com_rec (gen_asgn : pub_vars -> G com)
                     (gen_aread : pub_vars -> pub_arrs -> G com)
                     (gen_awrite : pub_vars -> pub_arrs -> G com)
                     (P:pub_vars) (PA:pub_arrs) (sz:nat) : G com :=
  match sz with
  | O => freq [(1, ret Skip);
               (4, thunkGen (fun _ => gen_asgn P));
               (4, thunkGen (fun _ => gen_aread P PA));
               (4, thunkGen (fun _ => gen_awrite P PA))]
  | S sz' =>
      freq [ (1, ret Skip);
             (sz, thunkGen (fun _ => gen_asgn P));
             (sz, thunkGen (fun _ => gen_aread P PA));
             (sz, thunkGen (fun _ => gen_awrite P PA));
             (2*sz, thunkGen (fun _ =>
                    liftM2 Seq (gen_com_rec gen_asgn gen_aread gen_awrite P PA sz')
                               (gen_com_rec gen_asgn gen_aread gen_awrite P PA sz')));
             (sz, thunkGen (fun _ =>
                  b <- arbitrarySized 1;;
                  liftM3 If (ret b)
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b))
                                 (gen_aread_in_ctx gen_aread (label_of_bexp P b))
                                 (gen_awrite_in_ctx gen_awrite (label_of_bexp P b))
                                 P PA sz')
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b))
                                 (gen_aread_in_ctx gen_aread (label_of_bexp P b))
                                 (gen_awrite_in_ctx gen_awrite (label_of_bexp P b))
                                 P PA sz')));
             (div sz 2, thunkGen (fun _ =>
                  b <- arbitrarySized 1;;
                  liftM2 While (ret b)
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b))
                                 (gen_aread_in_ctx gen_aread (label_of_bexp P b))
                                 (gen_awrite_in_ctx gen_aread (label_of_bexp P b))
                       P PA sz')))]
  end.

Definition gen_wt_com := gen_com_rec gen_secure_asgn gen_secure_aread gen_secure_awrite.

Definition AllPub : pub_vars := (_!-> true).

Definition gen_com := gen_wt_com AllPub AllPub.

Sample gen_pub_vars.

Definition someP := (false, [("X0", false); ("X1", true); ("X2", true);
                             ("X3", true); ("X4", false); ("X5", false)])%string.

Sample gen_pub_arrs.

Definition somePA := (true, [("A0", true); ("A1", true); ("A2", false)])%string.

Sample (sized (gen_wt_com someP somePA)).

Sample (sized gen_com).

(* Preventing empty arrays *)
Definition gen_astate : G astate :=
  ld <- choose (1,10);;
  d <- vectorOf ld arbitrary;;
  l0 <- choose (1,10);;
  v0 <- vectorOf l0 arbitrary;;
  l1 <- choose (1,10);;
  v1 <- vectorOf l1 arbitrary;;
  l2 <- choose (1,10);;
  v2 <- vectorOf l2 arbitrary;;
  ret (d, [("A0",v0); ("A1",v1); ("A2",v2)]) % string.

(* Extract Constant defNumTests => "1000000". *)

(* We first validate that our generator produces well-typed terms *)

QuickChick (forAll gen_pub_vars (fun P =>
           (forAll gen_pub_arrs (fun PA =>
           (forAll (sized (gen_wt_com P PA)) (fun (c:com) =>
             wt_typechecker P PA public c)))))).

(* Noninterference for source sequential execution *)
QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>
    forAll (sized (gen_wt_com P PA)) (fun c =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    forAll gen_astate (fun a1 =>
    forAll (gen_pub_equiv_and_same_length PA a1) (fun a2 =>
      let r1 := cteval_engine 10 c s1 a1 in
      let r2 := cteval_engine 10 c s2 a2 in
      match (r1, r2) with
      | (Some (s1', a1', os1), Some (s2', a2', os2)) =>
          checker ((pub_equivb P s1' s2') && (pub_equivb_astate PA a1' a2'))
      | _ => checker tt (* discard *)
      end
  )))))))).

(* Noninterference for target speculative execution *)
Definition check_speculative_noninterference trans : Checker :=
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  let hardened := trans P c in
  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 =>
  let s1 := ("b" !-> 0; s1) in
  let s2 := ("b" !-> 0; s2) in
  forAll gen_astate (fun a1 =>
  forAll (gen_pub_equiv_and_same_length PA a1) (fun a2 =>
  let r1 := cteval_engine 10 c s1 a1 in
  let r2 := cteval_engine 10 c s2 a2 in
  match (r1, r2) with
  | (Some (s1', a1', os1'), Some (s2', a2', os2')) =>
      implication (obs_eqb os1' os2') (* <-- this is needed here; otherwise see counterexample below *)
        (forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100)
          (fun '(ds, s1', a1', b', os1) =>
             match spec_eval_engine hardened s2 a2 false ds with
             | Some (s2', a2', b'', os2) =>
                 conjoin [checker (Bool.eqb b' b'' && (pub_equivb P s1' s2'));
                          implication (Bool.eqb b' false) (* <-- needed since we don't (yet) mask all stores *)
                                      (pub_equivb_astate PA a1' a2')]
             | None => checker tt (* discard *)
             end))
  | _ => checker tt (* discard *)
  end))))))).

QuickChick (check_speculative_noninterference flex_slh).

(* Counterexample without implication (obs_eqb os1' os2') ... *)
(* (true, [("X0", true); ("X1", false); ("X2", false); ("X3", true); ("X4", true); ("X5", false)]) *)
(* (false, [("A0", true); ("A1", false); ("A2", true)]) *)
(* (while (~ (X1 > (0 - 1))) do (if true then skip else ((X0 <- A2[[4]]) ; skip) end) end) *)
(* (0, [("X0", 2); ("X1", 1); ("X2", 1); ("X3", 0); ("X4", 4); ("X5", 2)]) *)
(* (0, [("X5", 0); ("X4", 4); ("X3", 0); ("X2", 3); ("X1", 0); ("X0", 2)]) *)
(* ([0; 3; 4; 2; 1], [("A0", [3; 3; 2; 2; 1; 1]); ("A1", [2; 1]); ("A2", [1; 2; 4; 2; 2; 3; 4; 1; 3])]) *)
(* ([0; 3; 4; 2; 1], [("A2", [1; 2; 4; 2; 2; 3; 4; 1; 3]); ("A1", [3; 3]); ("A0", [3; 3; 2; 2; 1; 1])]) *)
(* (((([force; force; step; step], (0, [("b", 1); ("X0", 0); ("X0", 2); ("b", 1); ("b", 1); ("b", 0); ("X0", 2); ("X1", 1); ("X2", 1); ("X3", 0); ("X4", 4); ("X5", 2)])), ([0; 3; 4; 2; 1], [("A0", [3; 3; 2; 2; 1; 1]); ("A1", [2; 1]); ("A2", [1; 2; 4; 2; 2; 3; 4; 1; 3])])), true), [branch false; branch true; aread A2 4; branch false]) *)
(* *** Failed after 67 tests and 5 shrinks. (12 discards) *)

(* Testing flex_slh_relative_secure *)

Definition check_relative_security trans : Checker :=
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>

  forAll (sized (gen_wt_com P PA)) (fun c =>
  let hardened := trans P c in

  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 =>
  let s1 := ("b" !-> 0; s1) in
  let s2 := ("b" !-> 0; s2) in

  forAll gen_astate (fun a1 =>
  forAll (gen_pub_equiv_and_same_length PA a1) (fun a2 =>
  let r1 := cteval_engine 10 c s1 a1 in
  let r2 := cteval_engine 10 c s2 a2 in
  match (r1, r2) with
  | (Some (s1', a1', os1'), Some (s2', a2', os2')) =>
      collect (show (List.length os1')) (
      implication (obs_eqb os1' os2')
        (forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100)
           (fun '(ds, s1', a1', b', os1) =>
              match spec_eval_engine hardened s2 a2 false ds with
              | Some (s2', a2', b'', os2) => checker (obs_eqb os1 os2)
              | None => checker tt (* discard *)
              end)))
  | _ => checker tt (* discard *)
  end))))))).

QuickChick (check_relative_security flex_slh).

(* Also testing Gilles' lemma here, not for ideal semantics, but for the translation *)

Definition check_gilles_lemma trans : Checker :=
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>

  forAll (sized (gen_wt_com P PA)) (fun c =>
  let hardened := trans P c in

  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 =>
  let s1 := ("b" !-> 1; s1) in
  let s2 := ("b" !-> 1; s2) in
  forAll gen_astate (fun a1 =>
  forAll gen_astate (fun a2 => (* same length not needed? *)
  forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100)
    (fun '(ds, s1', a1', b', os1) =>
       match spec_eval_engine hardened s2 a2 false ds with
       | Some (s2', a2', b'', os2) => checker (obs_eqb os1 os2)
       | None => checker tt (* discard *)
       end)))))))).

QuickChick (check_gilles_lemma flex_slh).

(* Directly testing also the top-level statement for Ultimate SLH,
   even if it is just a special case where all things are private.  *)

(* TODO: Discards are the biggest problem for this one, but there is hope of improving this later:
   https://secure-compilation.zulipchat.com/#narrow/stream/436285-speculation/topic/Testing.20Ultimate.20SLH *)

Fixpoint ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ ultimate_slh c1; ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c1
                          else "b" := ("b" = 0 && be) ? 1 : "b"; ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c end;
         "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

QuickChick (check_relative_security (fun _ => ultimate_slh)).

(* Also testing Gilles' lemma, not for ideal semantics, but for the translation *)
QuickChick (check_gilles_lemma (fun _ => ultimate_slh)).

(** * Standard SLH -- INSECURE! SHOULD FAIL! *)
Definition slh := sel_slh AllPub.
QuickChick (check_relative_security (fun _ => slh)).

(* Also testing Gilles' lemma -- SHOULD FAIL! *)
QuickChick (check_gilles_lemma (fun _ => slh)).

(** * Exorcising Spectre SLH -- INSECURE! SHOULD FAIL! *)
