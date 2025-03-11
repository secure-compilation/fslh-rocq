(** * Flow-Sensitive, Flexible Value SLH *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps SpecCT UltimateSLH_optimized FlexSLH FlexVSLH.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

(** * Flow-sensitive IFC tracking for flex_slh *)

(* Since we want to apply flex_slh to all programs, without rejecting anything
   as "ill-typed", we implement flow-sensitive static IFC tracking: *)

Inductive acom : Type :=
  | ASkip
  | AAsgn (x : string) (e : aexp)
  | ASeq (c1 c2 : acom)
  | AIf (be : bexp) (lbe : label) (c1 c2 : acom)
  | AWhile (be : bexp) (lbe : label) (c : acom)
  | AARead (x : string) (lx : label) (a : string) (i : aexp)  (li : label)
  | AAWrite (a : string) (i : aexp) (li : label) (e : aexp)
  | ABranch (lbl:label) (c:acom).

Declare Custom Entry acom.

Notation "'<[' e ']>'" := e (at level 0, e custom acom at level 99) : com_scope.
Notation "( x )" := x (in custom acom, x at level 99) : com_scope.
Notation "x" := x (in custom acom at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom acom at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Notation "'skip'"  :=
  ASkip (in custom acom at level 0) : com_scope.
Notation "x := y"  :=
  (AAsgn x y)
    (in custom acom at level 0, x constr at level 0,
      y custom acom at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (ASeq x y)
    (in custom acom at level 90, right associativity) : com_scope.
Notation "'if' x '@' lbe 'then' y 'else' z 'end'" :=
  (AIf x lbe y z)
    (in custom acom at level 89, x custom acom at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x '@' lbe 'do' y 'end'" :=
  (AWhile x lbe y)
    (in custom acom at level 89, x custom acom at level 99, y at level 99) : com_scope.
Notation "x '@@' lx '<-' a '[[' i '@' li ']]'"  :=
  (AARead x lx a i li)
     (in custom acom at level 0, x constr at level 0,
      a at level 85, i custom acom at level 85, no associativity) : com_scope.
Notation "a '[' i '@' li  ']'  '<-' e"  :=
  (AAWrite a i li e)
     (in custom acom at level 0, a constr at level 0,
      i custom acom at level 0, e custom acom at level 85,
         no associativity) : com_scope.
Notation "'branch' l c"  :=
  (ABranch l c) (in custom acom at level 91, l constr at level 0, c custom acom) : com_scope.

Fixpoint erase (ac:acom) : com :=
  match ac with
  | <[ skip ]> => <{skip}>
  | <[ X := ae ]> => <{X := ae}>
  | <[ ac1 ; ac2 ]> => <{ erase ac1; erase ac2 }>
  | <[ if be@lbe then ac1 else ac2 end ]> => <{ if be then erase ac1
                                                      else erase ac2 end }>
  | <[ while be @ lbe do ac1 end ]> => <{ while be do erase ac1 end }>
  | <[ X@@lx <- a[[i@li]] ]> => <{ X <- a[[i]] }>
  | <[ a[i@li] <- e ]> => <{ a[i] <- e }>
  | <[ branch l ac1 ]> => <{ erase ac1 }>
  end.

Definition join_pub_vars (P1 P2: pub_vars) : pub_vars :=
  fun x => join (P1 x) (P2 x).

Definition str_nodup := nodup string_dec.

Fixpoint assigned_vars c :=
  match c with
  | <{ skip }> | <{ _ [_] <- _ }> => []
  | <{ X := _ }> | <{ X <- _ [[_]] }> => [X]
  | <{ c1; c2 }>
  | <{ if _ then c1 else c2 end }> => str_nodup (assigned_vars c1 ++ assigned_vars c2)
  | <{ while _ do c end }> => assigned_vars c
  end.

Fixpoint assigned_arrs c :=
  match c with
  | <{ skip }>
  | <{ _ := _ }>
  | <{ _ <- _ [[_]] }> => []
  | <{ c1; c2 }>
  | <{ if _ then c1 else c2 end }> => str_nodup (assigned_arrs c1 ++ assigned_arrs c2)
  | <{ while _ do c end }> => assigned_arrs c
  | <{ a[_] <- _ }> => [a]
  end.

Definition list_eqb l1 l2 := if list_eq_dec string_dec l1 l2 then true else false.

Fixpoint static_tracking_while (static_tracking : pub_vars -> pub_arrs -> label -> (acom * pub_vars * pub_arrs))
      (P : pub_vars) (PA : pub_arrs) (pc : label) (i : nat) (be : bexp) (vars arrs pvars parrs : list string) :=
  let lbe := label_of_bexp P be in
  let '(ac, P1, PA1) := static_tracking P PA (join pc lbe) in
  let P1 := join_pub_vars P P1 in
  let PA1 := join_pub_vars PA PA1 in
  let pvars1 := filter P1 vars in
  let parrs1 := filter PA1 arrs in
  let stop := (list_eqb pvars pvars1) && (list_eqb parrs parrs1) in
    (* Stopping if a fixpoint was already reached *)
  match i, stop with
  | _, true | 0, _ => (P1, PA1, lbe, ac)
  | S i, false => static_tracking_while static_tracking P1 PA1 pc i be vars arrs pvars1 parrs1
  end.

Fixpoint static_tracking (c:com) (P:pub_vars) (PA:pub_arrs) (pc:label)
  : (acom*pub_vars*pub_arrs) :=
  match c with
  | <{ skip }> => (<[skip]>, P, PA)
  | <{ x := ae }> => (<[x := ae]>, x !-> (join pc (label_of_aexp P ae)); P, PA)
  | <{ c1; c2 }> => let '(ac1, P1, PA1) := static_tracking c1 P PA pc in
                    let '(ac2, P2, PA2) := static_tracking c2 P1 PA1 pc in
                     (<[ ac1; ac2 ]>, P2, PA2)
  | <{ if be then c1 else c2 end }> =>
      let lbe := label_of_bexp P be in
      let '(ac1, P1, PA1) := static_tracking c1 P PA (join pc lbe) in
      let '(ac2, P2, PA2) := static_tracking c2 P PA (join pc lbe) in
      (<[ if be@lbe then ac1 else ac2 end ]>, join_pub_vars P1 P2, join_pub_vars PA1 PA2)
  | <{ while be do c1 end }> =>
      let vars := assigned_vars c1 in
      let arrs := assigned_arrs c1 in
      let pvars := filter P vars in
      let parrs := filter PA arrs in
      let max_iters := length vars + length arrs in
      let '(P', PA', lbe, ac1) := static_tracking_while (static_tracking c1) P PA pc max_iters be vars arrs pvars parrs in
      (<[ while be@lbe do ac1 end ]>, P', PA')
  | <{ X <- a[[i]] }> =>
      let li := label_of_aexp P i in
      let lx := join pc (join li (PA a)) in
      (<[ X@@lx <- a[[i@li]] ]>, X !-> lx; P, PA)
  | <{ a[i] <- e }> =>
      let li := label_of_aexp P i in
      let la := join (PA a) (join pc (join li (label_of_aexp P e))) in
      (* It seems likely that the arrays will all become private quite quickly *)
      (<[ a[i@li] <- e ]>, P, a !-> la; PA)
  end.

Fixpoint static_tracking_acom ac P PA pc :=
  match ac with
  | <[ skip ]> => (<[skip]>, P, PA)
  | <[ x := ae ]> => (<[x := ae]>, x !-> (join pc (label_of_aexp P ae)); P, PA)
  | <[ c1; c2 ]> => let '(ac1, P1, PA1) := static_tracking_acom c1 P PA pc in
                    let '(ac2, P2, PA2) := static_tracking_acom c2 P1 PA1 pc in
                     (<[ ac1; ac2 ]>, P2, PA2)
  | <[ if be@_ then c1 else c2 end ]> =>
      let lbe := label_of_bexp P be in
      let '(ac1, P1, PA1) := static_tracking_acom c1 P PA (join pc lbe) in
      let '(ac2, P2, PA2) := static_tracking_acom c2 P PA (join pc lbe) in
      (<[ if be@lbe then ac1 else ac2 end ]>, join_pub_vars P1 P2, join_pub_vars PA1 PA2)
  | <[ while be@_ do c1 end ]> =>
      let vars := assigned_vars (erase c1) in
      let arrs := assigned_arrs (erase c1) in
      let pvars := filter P vars in
      let parrs := filter PA arrs in
      let max_iters := length vars + length arrs in
      let '(P', PA', lbe, ac1) := static_tracking_while (static_tracking_acom c1) P PA pc max_iters be vars arrs pvars parrs in
      (<[ while be@lbe do ac1 end ]>, P', PA')
  | <[ X@@_ <- a[[i@_]] ]> =>
      let li := label_of_aexp P i in
      let lx := join pc (join li (PA a)) in
      (<[ X@@lx <- a[[i@li]] ]>, X !-> lx; P, PA)
  | <[ a[i@_] <- e ]> =>
      let li := label_of_aexp P i in
      let la := join (PA a) (join pc (join li (label_of_aexp P e))) in
      (* It seems likely that the arrays will all become private quite quickly *)
      (<[ a[i@li] <- e ]>, P, a !-> la; PA)
  | <[ branch l c ]> => let '(ac, P, PA) := static_tracking_acom c P PA pc in
                      (<[ branch l ac ]>, P, PA)
  end.

Lemma static_tracking_while_invariant : forall ac P' PA' pc' f P PA pc i be vars arrs pvars parrs (R : acom -> Prop),
  (forall ac' P PA P1 PA1 pc, f P PA pc = (ac', P1, PA1) -> R ac') ->
  static_tracking_while f P PA pc i be vars arrs pvars parrs = (P', PA', pc', ac) ->
  R ac.
Proof.
  intros until i. revert f P PA pc P' PA' pc'. induction i; simpl; intros.
  + destruct (f P PA (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1) eqn:Heq1.
    eapply H. rewrite Heq1.
    destruct (list_eqb pvars (filter (join_pub_vars P P1) vars) && list_eqb parrs (filter (join_pub_vars PA PA1) arrs)); now invert H0.
  + destruct (f P PA (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1) eqn:Heq.
    destruct (list_eqb pvars (filter (join_pub_vars P P1) vars) && list_eqb parrs (filter (join_pub_vars PA PA1) arrs)).
    - invert H0. eapply H, Heq.
    - eapply IHi; eassumption.
Qed.

Lemma erase_static_tracking : forall c ac P PA P' PA' pc,
  static_tracking c P PA pc = (ac, P', PA') ->
  erase ac = c.
Proof.
  induction c; simpl; intros; try (now invert H; auto).
  + destruct (static_tracking c1 P PA pc) as ((ac1&P1)&PA1) eqn:Heq1.
    destruct (static_tracking c2 P1 PA1 pc) as ((ac2&P2)&PA2) eqn:Heq2.
    invert H. erewrite <- IHc1; [|eassumption]. erewrite <- IHc2; [tauto|eassumption].
  + destruct (static_tracking c1 P PA (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1) eqn:Heq1.
    destruct (static_tracking c2 P PA (join pc (label_of_bexp P be))) as ((ac2&P2)&PA2) eqn:Heq2.
    invert H. erewrite <- IHc1; [|eassumption]. erewrite <- IHc2; [tauto|eassumption].
  + destruct (static_tracking_while (static_tracking c) P PA pc (length (assigned_vars c) + length (assigned_arrs c)) be (assigned_vars c)
      (assigned_arrs c) (filter P (assigned_vars c)) (filter PA (assigned_arrs c))) as (((P1&PA1)&pc1)&ac1) eqn:Heq.
    invert H. simpl. eapply static_tracking_while_invariant in Heq; [|apply IHc]. now rewrite Heq.
Qed.

Fixpoint flex_vslh_acom ac :=
  match ac with
  | <[ skip ]> => <{ skip }>
  | <[ X := ae ]> => <{ X := ae }>
  | <[ ac1; ac2 ]> => <{ flex_vslh_acom ac1; flex_vslh_acom ac2 }>
  | <[ if be@lbe then ac1 else ac2 end ]> =>
      let be' := if lbe then be else <{ "b" = 0 && be }> in
      <{ if be' then "b" := be' ? "b" : 1; flex_vslh_acom ac1 else
                     "b" := be' ? 1 : "b"; flex_vslh_acom ac2 end }>
  | <[ while be@lbe do ac end ]> =>
      let be' := if lbe then be else <{ "b" = 0 && be }> in
      <{ while be' do "b" := be' ? "b" : 1; flex_vslh_acom ac end; "b" := be' ? 1 : "b" }>
  | <[ X@@lx <- a[[i@li]] ]> =>
      let i' := if li && negb lx then i else <{ ("b" = 1) ? 0 : i }> in
      if lx && li then <{ X <- a[[i]]; X := ("b" = 1) ? 0 : X }> else <{ X <- a[[i']] }>
  | <[ a[i@li] <- e ]> => let i' := if li then i else <{ ("b" = 1) ? 0 : i }> in
      <{ a[i'] <- e }>
  | <[ branch l ac1 ]> => <{ flex_vslh_acom ac1 }> (* unreachable anyway *)
  end.

Definition fs_flex_vslh P PA c :=
  let '(ac, _, _) := static_tracking c P PA public in
  flex_vslh_acom ac.

(** * Ideal small-step evaluation *)

Inductive terminal : acom -> Prop :=
  | Terminal_Skip : terminal <[ skip ]>
  | Terminal_Branch : forall l c, terminal c -> terminal <[ branch l c ]>.

Reserved Notation
  "'<[[' c , st , ast , b , pc , P , PA ']]>' '-->i_' ds '^^' os '<[[' ct , stt , astt , bt , pct , Pt , PAt ']]>'"
  (at level 40, c custom acom at level 99, ct custom acom at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step :
    acom -> state -> astate -> bool -> label -> pub_vars -> pub_arrs ->
    acom -> state -> astate -> bool -> label -> pub_vars -> pub_arrs -> dirs -> obs -> Prop :=
  | ISM_Asgn : forall X ae n st ast b pc P PA,
      aeval st ae = n ->
      <[[X := ae, st, ast, b, pc, P, PA]]> -->i_[]^^[] <[[skip, X !-> n; st, ast, b, pc, X !-> (join pc (label_of_aexp P ae)); P, PA]]>
  | ISM_Seq : forall c1 st ast b ds os c1t stt astt bt c2 pc P PA pc' P' PA',
      <[[c1, st, ast, b, pc, P, PA]]>  -->i_ds^^os <[[c1t, stt, astt, bt, pc', P', PA']]>  ->
      <[[(c1;c2), st, ast, b, pc, P, PA]]>  -->i_ds^^os <[[(c1t;c2), stt, astt, bt, pc', P', PA']]>
  | ISM_Seq_Skip : forall st ast b c1 c2 pc P PA,
      terminal c1 ->
      <[[(c1;c2), st, ast, b, pc, P, PA]]>  -->i_[]^^[] <[[c2, st, ast, b, pc, P, PA]]>
  | ISM_If : forall be ct cf st ast b c' b' lbe pc P PA,
      b' = (lbe || negb b) && beval st be ->
      c' = (if b' then ct else cf) ->
      <[[if be@lbe then ct else cf end, st, ast, b, pc, P, PA]]> -->i_[DStep]^^[OBranch b'] <[[branch pc c', st, ast, b, join pc lbe, P, PA]]>
  | ISM_If_F : forall be ct cf st ast b c' b' lbe pc P PA,
      b' = (lbe || negb b) && beval st be ->
      c' = (if b' then cf else ct) ->
      <[[if be@lbe then ct else cf end, st, ast, b, pc, P, PA]]> -->i_[DForce]^^[OBranch b'] <[[branch pc c', st, ast, true, join pc lbe, P, PA]]>
  | ISM_While : forall be c st ast b lbe c' pc P PA,
      c' = <[ if be@lbe then c; while be@lbe do c end else skip end ]> ->
      <[[while be@lbe do c end, st, ast, b, pc, P, PA]]> -->i_[]^^[] <[[c', st, ast, b, pc, P, PA]]>
  | ISM_ARead : forall X a ie st ast (b :bool) i li lX v pc P PA,
      (if (negb li) && b then 0 else (aeval st ie)) = i ->
      (if lX && li && b then 0 else nth i (ast a) 0) = v ->
      i < length (ast a) ->
      <[[X@@lX <- a[[ie@li]], st, ast, b, pc, P, PA]]> -->i_[DStep]^^[OARead a i]
            <[[skip, X !-> v; st, ast, b, pc, X !-> lX; P, PA]]>
  | ISM_ARead_U : forall X a ie st ast i a' i' v (lX:label) pc P PA,
      aeval st ie = i ->
      v = (if lX then 0 else nth i' (ast a') 0) ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <[[X@@lX <- a[[ie@public]], st, ast, true, pc, P, PA]]> -->i_[DLoad a' i']^^[OARead a i]
            <[[skip, X !-> v; st, ast, true, pc, X !-> lX; P, PA]]>
  | ISM_Write : forall a ie e st ast (b :bool) i n li i' la pc P PA,
      aeval st e = n ->
      aeval st ie = i ->
      (if b && negb li then 0 else i) = i' ->
      la = join (PA a) (join pc (join li (label_of_aexp P e))) ->
      i' < length (ast a) ->
      <[[a[ie@li] <- e, st, ast, b, pc, P, PA]]> -->i_[DStep]^^[OAWrite a i']
            <[[skip, st, a !-> upd i' (ast a) n; ast, b, pc, P, a !-> la; PA]]>
  | ISM_Write_U : forall a ie e st ast i n a' i' la pc P PA,
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      la = join (PA a) (join pc (label_of_aexp P e)) ->
      <[[a[ie@public] <- e, st, ast, true, pc, P, PA]]> -->i_[DStore a' i']^^[OAWrite a i]
            <[[skip, st, a' !-> upd i' (ast a') n; ast, true, pc, P, a !-> la; PA]]>
  | ISM_Branch : forall c1 st ast b ds os c1t stt astt bt pc pc' P PA pct Pt PAt,
      <[[c1, st, ast, b, pc, P, PA]]>  -->i_ds^^os <[[c1t, stt, astt, bt, pct, Pt, PAt]]>  ->
      <[[branch pc' c1, st, ast, b, pc, P, PA]]>  -->i_ds^^os <[[branch pc' c1t, stt, astt, bt, pct, Pt, PAt]]>

    where "<[[ c , st , ast , b , pc , P , PA ]]> -->i_ ds ^^ os  <[[ ct ,  stt , astt , bt , pct , Pt , PAt ]]>" :=
    (ideal_eval_small_step c st ast b pc P PA ct stt astt bt pct Pt PAt ds os).

Reserved Notation
  "'<[[' c , st , ast , b , pc , P , PA ']]>' '-->i*_' ds '^^' os '<[[' ct , stt , astt , bt , pct , Pt , PAt ']]>'"
  (at level 40, c custom acom at level 99, ct custom acom at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (c:acom) (st:state) (ast:astate) (b:bool) (pc:label) (P:pub_vars) (PA:pub_arrs):
    acom -> state -> astate -> bool -> label -> pub_vars -> pub_arrs -> dirs -> obs -> Prop :=
  | multi_ideal_refl : <[[c, st, ast, b, pc, P, PA]]> -->i*_[]^^[] <[[c, st, ast, b, pc, P, PA]]>
  | multi_ideal_trans (c':acom) (st':state) (ast':astate) (b':bool)
                (c'':acom) (st'':state) (ast'':astate) (b'':bool) (pc' pc'':label) (P' P'':pub_vars) (PA' PA'':pub_arrs)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      <[[c, st, ast, b, pc, P, PA]]> -->i_ds1^^os1 <[[c', st', ast', b', pc', P', PA']]> ->
      <[[c', st', ast', b', pc', P', PA']]> -->i*_ds2^^os2 <[[c'', st'', ast'', b'', pc'', P'', PA'']]> ->
      <[[c, st, ast, b, pc, P, PA]]> -->i*_(ds1++ds2)^^(os1++os2) <[[c'', st'', ast'', b'', pc'', P'', PA'']]>

  where "<[[ c , st , ast , b , pc , P , PA ]]> -->i*_ ds ^^ os  <[[ ct ,  stt , astt , bt , pct , Pt , PAt ]]>" :=
    (multi_ideal c st ast b pc P PA ct stt astt bt pct Pt PAt ds os).

Definition ideal_same_obs ac st1 st2 ast1 ast2 P PA :=
  forall ds os1 os2 stt1 stt2 astt1 astt2 ac1 ac2 b1 b2 pc1 pc2 Pt1 PAt1 Pt2 PAt2,
    <[[ac, st1, ast1, false, public, P, PA]]> -->i*_ds^^os1 <[[ac1, stt1, astt1, b1, pc1, Pt1, PAt1]]> ->
    <[[ac, st2, ast2, false, public, P, PA]]> -->i*_ds^^os2 <[[ac2, stt2, astt2, b2, pc2, Pt2, PAt2]]> ->
    os1 = os2.

Lemma multi_ideal_trans_nil_l c st ast b c' st' ast' b' ct stt astt bt ds os pc pc' pct P PA P' PA' Pt PAt:
  <[[c, st, ast, b, pc, P, PA]]> -->i_[]^^[] <[[c', st', ast', b', pc', P', PA']]> ->
  <[[c', st', ast', b', pc', P', PA']]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. rewrite <- app_nil_l. rewrite <- app_nil_l with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_trans_nil_r c st ast b c' st' ast' b' ct stt astt bt ds os pc pc' pct P PA P' PA' Pt PAt:
  <[[c, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[c', st', ast', b', pc', P', PA']]> ->
  <[[c', st', ast', b', pc', P', PA']]> -->i*_[]^^[] <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_combined_executions :
  forall c st ast b ds cm stm astm bm os dst ct stt astt bt ost pc P PA pcm Pm PAm pct Pt PAt,
    <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[cm, stm, astm, bm, pcm, Pm, PAm]]> ->
    <[[cm, stm, astm, bm, pcm, Pm, PAm]]> -->i*_dst^^ost <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
    <[[c, st, ast, b, pc, P, PA]]> -->i*_(ds++dst)^^(os++ost) <[[ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. revert ct stt astt bt pct Pt PAt dst ost H0. induction H; simpl; intros; [tauto|].
  rewrite <- 2!app_assoc. eapply multi_ideal_trans.
  + eapply H.
  + now apply IHmulti_ideal.
Qed.

Lemma multi_ideal_add_snd_com : forall c st ast ct stt astt ds os c2 b bt pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[c;c2, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct;c2, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. induction H; repeat econstructor; eauto.
Qed.

Lemma multi_ideal_seq : forall ac1 ac2 acm st ast b stm astm bm ds os pc P PA pcm Pm PAm,
  <[[ac1; ac2, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[acm, stm, astm, bm, pcm, Pm, PAm]]> ->
  (exists st' ast' pc' P' PA' act b' ds1 ds2 os1 os2,
  terminal act /\ os = os1 ++ os2 /\ ds = ds1 ++ ds2 /\
  <[[ac1, st, ast, b, pc, P, PA]]> -->i*_ds1^^os1 <[[act, st', ast', b', pc', P', PA']]> /\
  <[[ac2, st', ast', b', pc', P', PA']]> -->i*_ds2^^os2 <[[acm, stm, astm, bm, pcm, Pm, PAm]]>) \/
  (exists ac', acm = <[ ac'; ac2 ]> /\
   <[[ac1, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ac', stm, astm, bm, pcm, Pm, PAm]]>).
Proof.
  intros. remember <[ ac1; ac2 ]> as ac. revert ac1 ac2 Heqac.
  induction H; intros; subst.
  { right. repeat eexists. constructor. }
  invert H.
  + edestruct IHmulti_ideal; [reflexivity|..].
    - destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&->&->&?&?).
      left. rewrite !app_assoc. repeat eexists; [|econstructor|]; eassumption.
    - do 2 destruct H. subst. clear IHmulti_ideal.
      right. repeat eexists. econstructor; eassumption.
  + left. repeat eexists; [|constructor|eassumption]. tauto.
Qed.

Lemma ideal_eval_small_step_spec_needs_force : forall c st ast ct stt astt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i_ds^^os <[[ct, stt, astt, true, pct, Pt, PAt]]> ->
  ds = [DForce].
Proof.
  intros. remember false as b. remember true as bt. revert Heqb Heqbt.
  now induction H; intros; subst; try discriminate; try reflexivity; apply IHideal_eval_small_step.
Qed.

Lemma multi_ideal_spec_needs_force : forall c st ast ct stt astt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, true, pct, Pt, PAt]]> ->
  In DForce ds.
Proof.
  intros. remember false as b. remember true as bt. revert Heqb Heqbt.
  induction H; intros; subst; [discriminate|]. apply in_or_app.
  destruct b'.
  + apply ideal_eval_small_step_spec_needs_force in H. subst. left. now left.
  + right. now apply IHmulti_ideal.
Qed.

Lemma ideal_eval_seq_eval : forall c st ast ct stt astt bt n os pc P PA pct Pt PAt,
 <[[c, st, ast, false, pc, P, PA]]> -->i_ repeat DStep n ^^ os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <((erase c, st, ast))> -->^os <((erase ct, stt, astt))>.
Proof.
  intros. remember false as b in H. remember (repeat DStep n) as ds in H. revert Heqb Heqds.
  induction H; intros; subst; try discriminate; try now econstructor.
  + constructor. now apply IHideal_eval_small_step.
  + induction H; simpl in *; [constructor|tauto].
  + rewrite orb_true_r. simpl. replace (erase (if beval st be then ct else cf)) with (if beval st be then erase ct else erase cf) by now destruct (beval st be). constructor.
  + symmetry in Heqds. change ([DForce]) with ([] ++ [DForce]) in Heqds.
    now apply repeat_eq_elt in Heqds.
  + rewrite ?andb_false_r in *. now constructor.
  + now apply IHideal_eval_small_step.
Qed.

Lemma multi_ideal_branch : forall c st ast b ct stt astt bt ds os l pc P PA pct Pt PAt,
  <[[ c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[ branch l c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ branch l ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. induction H; [constructor|].
  repeat econstructor; eassumption.
Qed.

Lemma multi_ideal_multi_seq : forall c st ast ct stt astt bt n os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ repeat DStep n ^^ os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <((erase c, st, ast ))> -->*^os <((erase ct, stt, astt))>.
Proof.
  intros. remember false as b in H. remember (repeat DStep n) as ds in H. revert n Heqb Heqds.
  induction H; intros; subst; [constructor|].
  symmetry in Heqds. apply repeat_eq_app in Heqds. destruct Heqds.
  remember (length ds1) as n1. remember (length ds2) as n2. clear Heqn1 Heqn2 H0. subst.
  destruct b'. { apply ideal_eval_small_step_spec_needs_force in H. change ([DForce]) with ([] ++ [DForce]) in H. now apply repeat_eq_elt in H. }
  apply ideal_eval_seq_eval in H. econstructor; [eassumption|].
  now eapply IHmulti_ideal; eauto.
Qed.

Lemma ideal_eval_small_step_obs_length : forall c st ast b ds ct stt astt bt os pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  length ds = length os.
Proof. intros. induction H; simpl; auto. Qed.

Lemma ideal_terminal_no_step : forall c st ast b ct stt astt bt ds os pc P PA pct Pt PAt,
  terminal c ->
  <[[ c, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[ ct, stt, astt, bt, pct, Pt, PAt]]> ->
  False.
Proof. intros. revert ct H0. induction H; intros; [invert H0|invert H0]. eapply IHterminal, H18. Qed.

Lemma ideal_eval_small_step_same_length : forall c st1 st2 ast1 ast2 b1 b2 ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 ds1 ds2
    pc1 P1 PA1 pc2 P2 PA2 pct1 Pt1 PAt1 pct2 Pt2 PAt2,
  <[[c, st1, ast1, b1, pc1, P1, PA1]]> -->i_ds1^^os1 <[[ct1, stt1, astt1, bt1, pct1, Pt1, PAt1]]> ->
  <[[c, st2, ast2, b2, pc2, P2, PA2]]> -->i_ds2^^os2 <[[ct2, stt2, astt2, bt2, pct2, Pt2, PAt2]]> ->
  length ds1 = length ds2.
Proof.
  intros. revert st2 ast2 b2 ct2 stt2 astt2 bt2 pc2 P2 PA2 pct2 Pt2 PAt2 H0.
  induction H; simpl; intros.
  + now invert H0.
  + invert H0; [|now apply ideal_terminal_no_step in H].
    eapply IHideal_eval_small_step; eassumption.
  + invert H0; [now apply ideal_terminal_no_step in H18|reflexivity].
  + now invert H1.
  + now invert H1.
  + now invert H0.
  + now invert H2.
  + now invert H3.
  + now invert H4.
  + now invert H4.
  + invert H0. eapply IHideal_eval_small_step, H18.
Qed.

Lemma multi_ideal_obs_length : forall c st ast b ds ct stt astt bt os pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  length ds = length os.
Proof. intros. induction H; [tauto|].
  do 2 rewrite app_length. apply ideal_eval_small_step_obs_length in H.
  auto.
Qed.

Lemma ideal_eval_small_step_spec_bit_monotonic : forall c st ast ds ct stt astt bt os pc P PA pct Pt PAt,
  <[[c, st, ast, true, pc, P, PA]]> -->i_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  bt = true.
Proof.
  intros. remember true as b eqn:Eqb.
  induction H; subst; eauto.
Qed.

Lemma multi_ideal_spec_bit_monotonic : forall c st ast ds ct stt astt bt os pc P PA pct Pt PAt,
  <[[c, st, ast, true, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  bt = true.
Proof.
  intros. remember true as b eqn:Eqb.
  induction H; subst; eauto. apply ideal_eval_small_step_spec_bit_monotonic in H; subst.
  auto.
Qed.

Lemma ideal_eval_small_step_no_spec : forall c st ast ct stt astt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i_ds^^os <[[ct, stt, astt, false, pct, Pt, PAt]]> ->
  ds = [DStep] \/ ds = [].
Proof.
  intros. remember false as b in H at 1. remember false as bt in H. revert Heqb Heqbt.
  induction H; intros; subst; try discriminate; (try now left); (try now right);
    now apply IHideal_eval_small_step.
Qed.

Lemma multi_ideal_no_spec : forall c st ast ct stt astt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, false, pct, Pt, PAt]]> ->
  exists n, ds = repeat DStep n.
Proof.
  intros. remember false as b in H at 1. remember false as bt in H. revert Heqb Heqbt.
  induction H; intros; subst; [now exists 0|].
  destruct b'; [now apply multi_ideal_spec_bit_monotonic in H0|].
  apply ideal_eval_small_step_no_spec in H. destruct IHmulti_ideal as (n&->); [reflexivity..|].
  destruct H; subst; [|now exists n].
  exists (1 + n). now rewrite repeat_app.
Qed.

Lemma multi_ideal_spec_bit_deterministic : forall c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2
  pc1 pc2 P1 P2 PA1 PA2 pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  <[[ c, st1, ast1, b, pc1, P1, PA1 ]]> -->i*_ ds ^^ os1 <[[ c1, stt1, astt1, bt1, pct1, Pt1, PAt1 ]]> ->
  <[[ c, st2, ast2, b, pc2, P2, PA2 ]]> -->i*_ ds ^^ os2 <[[ c2, stt2, astt2, bt2, pct2, Pt2, PAt2 ]]> ->
  bt1 = bt2.
Proof.
  intros. destruct b.
  + apply multi_ideal_spec_bit_monotonic in H, H0. congruence.
  + destruct bt1, bt2; try reflexivity.
    1:rename H into H1. 1:rename H0 into H2.
    2:rename H0 into H1. 2:rename H into H2.
    all:apply multi_ideal_no_spec in H2.
    all:apply multi_ideal_spec_needs_force in H1.
    all:destruct H2 as (n&->).
    all:now apply repeat_spec in H1.
Qed.

Lemma ideal_eval_small_step_dirs_obs : forall c st ast b ct stt astt bt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i_ ds ^^ os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  (ds = [] /\ os = []) \/ (exists d o, ds = [d] /\ os = [o]).
Proof. intros. now induction H; eauto. Qed.

Lemma ideal_eval_small_step_silent_step : forall c st ast b ct stt astt bt pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i_ [] ^^ [] <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  b = bt /\ ast = astt /\ pc = pct /\ PA = PAt.
Proof. intros. remember [] as ds in H at 1. revert Heqds. now induction H; intros; eauto. Qed.

Lemma multi_ideal_factorize : forall c st ast b ct stt astt bt d ds os pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ (d :: ds) ^^ os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  exists c' st' ct' stt' astt' bt' o os' P' pct' Pt' PAt',
  os = o :: os' /\
  <[[c, st, ast, b, pc, P, PA]]> -->i*_[]^^[] <[[c', st', ast, b, pc, P', PA]]> /\
  <[[c', st', ast, b, pc, P', PA]]> -->i_[d]^^[o] <[[ct', stt', astt', bt', pct', Pt', PAt']]> /\
  <[[ct', stt', astt', bt', pct', Pt', PAt']]> -->i*_ds^^os' <[[ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. remember (d :: ds) as ds'. revert d ds Heqds'. induction H; intros; try discriminate.
  apply ideal_eval_small_step_dirs_obs in H as Heq.
  destruct Heq.
  + destruct H1. subst. simpl in Heqds'. subst. simpl.
    specialize (IHmulti_ideal d ds Logic.eq_refl).
    destruct IHmulti_ideal as (?&?&?&?&?&?&?&?&?&?&?&?&->&?&?&?).
    apply ideal_eval_small_step_silent_step in H as Heq. destruct Heq as (->&->&->&->).
    eapply multi_ideal_trans in H1; [|apply H]. simpl in H1. now eauto 20.
  + destruct H1 as (d'&o&->&->). simpl in Heqds'. invert Heqds'. simpl.
    repeat eexists; [|eassumption..]. now constructor.
Qed.

Lemma multi_ideal_preserves_seq_same_obs : forall c st1 st2 ast1 ast2 ct stt1 stt2 astt1 astt2 ds os1 os2
    pc1 pc2 P1 P2 PA1 PA2 pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  seq_same_obs (erase c) st1 st2 ast1 ast2 ->
  <[[c, st1, ast1, false, pc1, P1, PA1]]> -->i*_ds^^os1 <[[ct, stt1, astt1, false, pct1, Pt1, PAt1]]> ->
  <[[c, st2, ast2, false, pc2, P2, PA2]]> -->i*_ds^^os2 <[[ct, stt2, astt2, false, pct2, Pt2, PAt2]]> ->
  seq_same_obs (erase ct) stt1 stt2 astt1 astt2.
Proof.
  unfold seq_same_obs. intros.
  apply multi_ideal_obs_length in H0 as Heq, H1 as Heq'.
  rewrite Heq' in Heq. clear Heq'.
  apply multi_ideal_no_spec in H0 as Heq'.
  destruct Heq' as (n&->).
  apply multi_ideal_multi_seq in H0, H1.
  eapply H in H0 as Hpref; [|eassumption]. apply prefix_eq_length in Heq; [|tauto].
  subst. clear Hpref. eapply multi_seq_combined_executions in H2; [|eassumption].
  eapply multi_seq_combined_executions in H3; [|eassumption].
  eapply H in H2; [|eassumption]. destruct H2; apply prefix_append_front in H2; tauto.
Qed.

Lemma pub_equiv_join : forall {A} P P' (st st' : total_map A),
  pub_equiv P st st' ->
  pub_equiv (join_pub_vars P P') st st'.
Proof. intros. intros x Hx. apply andb_prop in Hx. now apply H. Qed.

Lemma join_pub_vars_sym : forall P P',
  join_pub_vars P P' = join_pub_vars P' P.
Proof. intros. apply FunctionalExtensionality.functional_extensionality. intro x. apply andb_comm. Qed.

(* if true@secret then x:=0 end, pub, [] -> *)
(* x:=0, secret, [pub] -> *)
(* skip, secret, [pub] -> *)

(* (if true@secret then x:=0 end);c1, pub, [] -> *)
(* x:=0;c1, secret, [pub] -> *)
(* skip;c1, secret, [pub] -> *)
(* c1, pub, [] *)

(* (if true@secret then x:=0;y:=1 end);c1, pub, [] -> *)
(* (x:=0;y:=1);c1, secret, [pub] -> *)
(* (skip;y:=1);c1, secret, [pub] ->  <-- we pop wrongly *)
(* y:=1;c1, pub, [] -> *)
(* skip;c1, pub, [] stuck *)

(* Catalin, but need new branch annotated command and in this version this takes extra steps: *)
(* - similar to: From Dynamic to Static and Back *)
(*   https://link.springer.com/chapter/10.1007/978-3-642-11486-1_30 *)
(* if true@secret then x:=0;y:=1 end);c1 -> *)
(* (x:=0;y:=1;branch pub);c1 *)

(* Leon, but need funny counting and need to know which branch we take -> need directions and observations: *)
(* if true@secret then x:=0;y:=1 end);c1, pub, [] -> *)
(* (x:=0;y:=1);c1, secret, [secret,pub] -> *)
(* (skip;y:=1);c1, secret, [secret,pub] -> *)
(* y:=1;c1, secret, [pub] -> *)
(* skip;c1, secret, [pub] -> *)
(* c1, pub, [] *)

(* Catalin V2, but need new branch annotated command, and in this version step_taints and ideal semantics merged: *)
(* if true@secret then x:=0;y:=1 end);c1, pub -> *)
(* (branch pub (x:=0;y:=1));c1, secret -> *)
(* (branch pub (skip;y:=1));c1, secret -> *)
(* (branch pub (y:=1));c1, secret -> *)
(* (branch pub skip);c1, secret -> *)
(* c1, pub *)

(* Together V3, but need new branch annotated command, yet step_taints and ideal semantics not merged: *)
(* if true@secret then x:=0;y:=1 end);c1, pub, [] -> *)
(* (branch (x:=0;y:=1));c1, secret, [pub] -> *)
(* (branch (skip;y:=1));c1, secret, [pub] -> *)
(* (branch (y:=1));c1, secret, [pub] -> *)
(* (branch skip);c1, secret, [pub] -> *)
(* c1, pub, [] *)

(*
Fixpoint ideal_step_taints ac P PA pc (pcs : list label) : pub_vars * pub_arrs * label * list label :=
  match ac with
  | <[ skip ]> => (P, PA, pc ,pcs)
  | <[ x := e ]> => (x !-> (join pc (label_of_aexp P e)); P, PA, pc, pcs)
  | <[ c1; c2 ]> => ideal_step_taints c1 P PA pc pcs
  | <[ if be@_lbe then c1 else c2 end ]> => (* the _lbe is the same as lbe, right? *)
      let lbe := label_of_bexp P be in
      (P, PA, join pc lbe, pc::pcs)
  | <[ while be@_lbe do c end ]> => (P, PA, pc, pcs)
  | <[ x@@_lx <- a[[i@li]] ]> => (* the _lx is the same as lx, right? *)
      let li := label_of_aexp P i in
      let lx := join pc (join li (PA a)) in
      (x !-> lx; P, PA, pc, pcs)
  | <[ a[i@_li] <- e ]> => (* the _li is the same as li, right? *)
      let li := label_of_aexp P i in
      let la := join (PA a) (join pc (join li (label_of_aexp P e))) in
      (P, a !-> la; PA, pc, pcs)
  | <[ branch l c ]> =>
      let fix unpop_stack c pc pcs :=
        match c, pcs with
        | <[skip]>, pc::pcs => (pc, pcs, true)
        | <[branch c]>, pc::pcs => unpop_stack c pc pcs
        | _, _ => (pc, pcs, false)
        end in
      let '(pc', pcs', success) := unpop_stack c pc pcs in
      if success then (P, PA, pc', pcs') else ideal_step_taints c P PA pc pcs
  end.
*)

Definition less_precise_vars (P1 P2:pub_vars) : Prop :=
  forall x, can_flow (P2 x) (P1 x) = true.

Fixpoint less_precise_acom (ac1 ac2 : acom) : Prop :=
  match ac1, ac2 with
  | <[ c11; c12 ]>, <[ c21;c22 ]> => less_precise_acom c11 c21 /\
                                     less_precise_acom c12 c22
  | <[ if be1@lbe1 then c11 else c12 end ]>,
    <[ if be2@lbe2 then c21 else c22 end ]> => be1 = be2 /\ can_flow lbe2 lbe1 = true /\
                                               less_precise_acom c11 c21 /\
                                               less_precise_acom c12 c22
  | <[ while be1@lbe1 do c1 end ]>,
    <[ while be2@lbe2 do c2 end ]> => be1 = be2 /\ can_flow lbe2 lbe1 = true /\
                                      less_precise_acom c1 c2
  | <[ x1@@lx1 <- a1[[i1@li1]] ]>,
    <[ x2@@lx2 <- a2[[i2@li2]] ]> => x1 = x2 /\ a1 = a2 /\ i1 = i2 /\
                                     can_flow lx2 lx1 = true /\ can_flow li2 li1 = true
  | <[ a1[i1@li1] <- e1 ]>,
    <[ a2[i2@li2] <- e2 ]> => a1 = a2 /\ i1 = i2 /\ e1 = e2 /\ can_flow li2 li1 = true
  | _, _ => ac1 = ac2
  end.

Definition less_precise (x1 x2 : acom * pub_vars * pub_arrs) : Prop :=
  let '(ac1,P1,PA1) := x1 in
  let '(ac2,P2,PA2) := x2 in
  less_precise_acom ac1 ac2 /\ less_precise_vars P1 P2 /\ less_precise_vars PA1 PA2.

Lemma pub_equiv_less_precise : forall (P P':pub_vars) {A:Type} (x1 x2:total_map A),
  pub_equiv P x1 x2 ->
  less_precise_vars P' P ->
  pub_equiv P' x1 x2.
Proof.
  intros. intros x P'x. unfold less_precise_vars, can_flow in H0. specialize (H0 x). apply H.
  now rewrite P'x, orb_false_r in H0.
Qed.

Lemma less_precise_vars_refl : forall P, less_precise_vars P P.
Proof. intros P x. now destruct (P x). Qed.

Lemma less_precise_acom_refl : forall ac, less_precise_acom ac ac.
Proof. induction ac; repeat econstructor; try destruct lbe; try destruct li; try destruct lx; tauto. Qed.

Inductive same_shape : acom -> acom -> Prop :=
  | Same_skip : same_shape <[skip]> <[skip]>
  | Same_asgn : forall x e, same_shape <[x:=e]> <[x:=e]>
  | Same_seq : forall c1 c2 c1' c2',
               same_shape c1 c1' ->
               same_shape c2 c2' ->
               same_shape <[c1; c2]> <[c1'; c2']>
  | Same_if : forall be lbe lbe' c1 c2 c1' c2',
               same_shape c1 c1' ->
               same_shape c2 c2' ->
               same_shape <[if be@lbe then c1 else c2 end]> <[if be@lbe' then c1' else c2' end]>
  | Same_while : forall be lbe lbe' c c',
               same_shape c c' ->
               same_shape <[while be@lbe do c end]> <[while be@lbe' do c' end]>
  | Same_aread : forall a x i lx lx' li li',
               same_shape <[x@@lx <- a[[i@li]] ]> <[x@@lx' <- a[[i@li']] ]>
  | Same_axrite : forall a i e li li',
               same_shape <[a[i@li] <- e]> <[a[i@li'] <- e]>
  | Same_branch : forall l c c',
               same_shape c c' ->
               same_shape <[branch l c]> <[branch l c']>.

Lemma static_tracking_acom_same_shape : forall c c' P PA Pt PAt pc,
  static_tracking_acom c P PA pc = (c', Pt, PAt) ->
  same_shape c c'.
Proof.
  induction c; simpl; intros; try now (invert H; constructor).
  + destruct (static_tracking_acom c1 P PA pc) as ((?&P')&PA') eqn:Heq.
    destruct (static_tracking_acom c2 P' PA' pc) as ((?&?)&?) eqn:Heq'.
    apply IHc1 in Heq. apply IHc2 in Heq'.
    invert H. now constructor.
  + destruct (static_tracking_acom c1 P PA (join pc (label_of_bexp P be))) as ((?&?)&?) eqn:Heq.
    destruct (static_tracking_acom c2 P PA (join pc (label_of_bexp P be))) as ((?&?)&?) eqn:Heq'.
    apply IHc1 in Heq. apply IHc2 in Heq'.
    invert H. now constructor.
  + destruct (static_tracking_while (static_tracking_acom c) P PA pc
        (length (assigned_vars (erase c)) + length (assigned_arrs (erase c))) be (assigned_vars (erase c))
        (assigned_arrs (erase c)) (filter P (assigned_vars (erase c))) (filter PA (assigned_arrs (erase c)))) as (((?&?)&?)&?) eqn:Heq.
    eapply static_tracking_while_invariant in Heq; [|apply IHc]. invert H.
    now constructor.
  + destruct (static_tracking_acom c P PA pc) as ((?&?)&?) eqn:Heq.
    apply IHc in Heq. invert H. now constructor.
Qed.

Lemma same_shape_static_tracking_acom : forall c c' P PA pc,
  same_shape c c' ->
  static_tracking_acom c P PA pc = static_tracking_acom c' P PA pc.
Proof. intros. revert P PA pc. induction H; simpl; intros; try tauto. Admitted.

Lemma ideal_eval_static_tracking_step :
  forall ac ds c P PA Pt PAt pc' P' PA' pc st ast b act stt astt bt os,
  static_tracking_acom c P PA pc = (ac, Pt, PAt) ->
  <[[ ac, st, ast, b, pc, P, PA ]]> -->i_ds^^os <[[ act, stt, astt, bt, pc', P', PA' ]]> ->
  less_precise (act, Pt, PAt) (static_tracking_acom act P' PA' pc').
Proof.
  intros. apply static_tracking_acom_same_shape in H as H'. revert c Pt PAt H H'.
  induction H0; simpl; intros; invert H'; simpl in *.
  + invert H0. split; [tauto|]. split; apply less_precise_vars_refl.
  + destruct (static_tracking_acom c0 P PA pc) as ((c1'&P1)&PA1) eqn:Heq1.
    destruct (static_tracking_acom c3 P1 PA1 pc) as ((c2'&P2)&PA2) eqn:Heq2.
    invert H. apply IHideal_eval_small_step in Heq1 as H'; [|tauto].
    destruct (static_tracking_acom c1t P' PA' pc') as ((act&P1t)&PA1t) eqn:Heq1t.
    destruct (static_tracking_acom c2 P1t PA1t pc') as ((act'&P2t)&PA2t) eqn:Heq2t.
    admit.
  + destruct (static_tracking_acom c0 P PA pc) as ((ac1&P1)&PA1) eqn:Heq1.
    destruct (static_tracking_acom c3 P1 PA1 pc) as ((ac2&P2)&PA2) eqn:Heq2.
    invert H0. revert c0 Heq1 H4.
    induction H; simpl; intros.
    { invert H4. invert Heq1. eapply same_shape_static_tracking_acom in H5.
      rewrite H5 in Heq2. rewrite Heq2. split; [apply less_precise_acom_refl|]. split; apply less_precise_vars_refl. }
    invert H4. simpl in Heq1. destruct (static_tracking_acom c1 P PA pc) as ((ac&P')&PA') eqn:Heq.
    invert Heq1. eapply IHterminal; eassumption.
Admitted.

Lemma ideal_eval_noninterferent :
  forall ac ds c P PA P' PA' pc st1 ast1 st2 ast2 b act1 act2 stt1 stt2 astt1 astt2 bt1 bt2 os pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  static_tracking c P PA pc = (ac, P', PA') ->
  pub_equiv P st1 st2 ->
  (b = false -> pub_equiv PA ast1 ast2) ->
  <[[ ac, st1, ast1, b, pc, P, PA ]]> -->i_ds^^os <[[ act1, stt1, astt1, bt1, pct1, Pt1, PAt1 ]]> ->
  <[[ ac, st2, ast2, b, pc, P, PA ]]> -->i_ds^^os <[[ act2, stt2, astt2, bt2, pct2, Pt2, PAt2 ]]> ->
  act1 = act2 /\ bt1 = bt2 /\ pct1 = pct2 /\ Pt1 = Pt2 /\ PAt1 = PAt2 /\
  pub_equiv Pt1 stt1 stt2 /\ (bt1 = false -> pub_equiv PAt1 astt1 astt2).
Admitted.

Definition acom_unused X ac := unused X (erase ac).

Lemma ideal_eval_preserves_nonempty_arrs : forall ac st ast b act stt astt bt ds os pc pct P Pt PA PAt,
  nonempty_arrs ast ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[act, stt, astt, bt, pct, Pt, PAt]]> ->
  nonempty_arrs astt.
Proof.
  intros.
  induction H0; [tauto..|now apply t_update_nonempty_arrs|now apply t_update_nonempty_arrs|tauto].
Qed.

Lemma multi_ideal_preserves_nonempty_arrs : forall ac st ast b act stt astt bt ds os pc pct P Pt PA PAt,
  nonempty_arrs ast ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, stt, astt, bt, pct, Pt, PAt]]> ->
  nonempty_arrs astt.
Proof.
  intros. induction H0; [tauto|].
  apply ideal_eval_preserves_nonempty_arrs in H0; tauto.
Qed.

Lemma ideal_unused_overwrite : forall ac st ast b act stt astt bt ds os X n pc pct P Pt PA PAt,
  acom_unused X ac ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[act, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[ac, X !-> n; st, ast, b, pc, P, PA]]> -->i_ds^^os <[[act, X !-> n; stt, astt, bt, pct, Pt, PAt]]> /\ acom_unused X act.
Proof.
  unfold acom_unused. intros. induction H0; simpl in *.
  + split; [|tauto]. rewrite t_update_permute; [|tauto]. constructor. now rewrite aeval_unused_update.
  + repeat constructor; tauto.
  + now repeat constructor.
  + split; [|rewrite_eq; destruct b'; tauto]. econstructor; [now rewrite beval_unused_update|tauto].
  + split; [|rewrite_eq; destruct b'; tauto]. econstructor; [now rewrite beval_unused_update|tauto].
  + repeat constructor; [tauto|subst]. simpl. tauto.
  + split; [|trivial]. rewrite t_update_permute; [|tauto]. econstructor; [now rewrite aeval_unused_update|eassumption|tauto].
  + split; [|trivial]. rewrite t_update_permute; [|tauto]. econstructor; [now rewrite aeval_unused_update|eassumption..].
  + split; [|trivial]. econstructor; [| |eassumption..]; now rewrite ?aeval_unused_update.
  + split; [|trivial]. econstructor; try tauto. all: now rewrite aeval_unused_update.
  + destruct IHideal_eval_small_step; [tauto|]. split; [|tauto]. now constructor.
Qed.

Lemma multi_ideal_unused_overwrite : forall ac st ast b act stt astt bt ds os X n pc pct P Pt PA PAt,
  acom_unused X ac ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[ac, X !-> n; st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, X !-> n; stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. induction H0; [constructor|].
  eapply ideal_unused_overwrite in H0; [|eassumption].
  destruct H0. now econstructor; eauto.
Qed.

Lemma multi_ideal_unused_update : forall ac st ast b act stt astt bt ds os X n pc pct P Pt PA PAt,
  acom_unused X ac ->
  <[[ac, X !-> n; st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, X !-> n; stt, astt, bt, pct, Pt, PAt]]> ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, X !-> st X; stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. eapply multi_ideal_unused_overwrite with (n:=st X) in H0; [|eassumption].
  now rewrite !t_update_shadow, t_update_same in H0.
Qed.

Fixpoint acom_size (c :acom) :nat :=
  match c with
  | <[ c1; c2 ]> => 1 + (acom_size c1) + (acom_size c2)
  (* For conditionals the maximum of both branches is tighter, but a
     looser bound based on blindly "counting all constructors"
     (commented here) works just as well, and is easier to explain on
     paper *)
  | <[ if _@_ then ct else cf end ]> => 1 + max (acom_size ct) (acom_size cf)
  (* | <{{ if be then ct else cf end }}> => 1 + (com_size ct) + (com_size cf) *)
  | <[ while _@_ do cw end ]> => 1 + (acom_size cw)
  | <[ branch l c ]> => 1 + acom_size c
  | _  => 1
  end.

Definition prog_size (c :acom) (ds :dirs) :nat := acom_size c + length ds.

(** The induction principle on [prog_size] *)

Lemma prog_size_ind :
  forall P : acom -> dirs -> Prop,
  (forall c ds,
    ( forall c' ds',
      prog_size c' ds' < prog_size c ds ->
      P c' ds') -> P c ds  ) ->
  (forall c ds, P c ds).
Proof.
  intros.
  remember (fun c_ds => P (fst c_ds) (snd c_ds)) as P'.
  replace (P c ds) with (P' (c, ds)) by now rewrite HeqP'.
  eapply measure_induction with (f:=fun c_ds => prog_size (fst c_ds) (snd c_ds)). intros. rewrite HeqP'.
  apply H. intros.
  remember (c', ds') as c_ds'.
  replace (P c' ds') with (P' c_ds') by now rewrite Heqc_ds', HeqP'.
  apply H0. now rewrite Heqc_ds'.
Qed.

(** The proof of [sel_slh_flag] *)

Lemma prog_size_monotonic: forall c1 ds1 c2 ds2,
  (acom_size c1 < acom_size c2 /\ length ds1 <= length ds2 ) \/
  (acom_size c1 <= acom_size c2 /\ length ds1 < length ds2) ->
  prog_size c1 ds1 < prog_size c2 ds2.
Proof.
  intros c1 ds1 c2 ds2 [ [Hcom Hdir] | [Hcom Hdir] ];
  unfold prog_size; lia.
Qed.

(** Based on the Lemma [prog_size_monotonic] we can build a tactic to solve
    the subgoals in the form of [prog_size c' ds' < prog_size c ds],
    which will be produced by [prog_size_ind].*)

Ltac prog_size_auto :=
  try ( apply prog_size_monotonic; left; split; simpl;
        [| repeat rewrite app_length]; lia );
  try ( apply prog_size_monotonic; right; split; simpl;
        [| repeat rewrite app_length]; lia);
  try ( apply prog_size_monotonic; left; split; simpl;
        [auto | repeat rewrite app_length; lia] ).

Ltac solve_refl :=
  now (do 5 eexists); split; [|split; [(try discriminate); (try now repeat econstructor)|(try discriminate); tauto] ]; rewrite ?t_update_shadow, t_update_same;
  repeat econstructor; (repeat rewrite_eq); rewrite ?andb_false_r; (try now apply label_of_exp_sound).

Lemma flex_slh_acom_bcc_generalized : forall ac st ast c' st' ast' os ds (b b' : bool) pc P PA,
  nonempty_arrs ast ->
  acom_unused "b" ac ->
  st "b" = (if b then 1 else 0) ->
  <((flex_vslh_acom ac, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists st'' ac' pc' P' PA',
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ac', "b" !-> st "b"; st'', ast', b', pc', P', PA']]> /\
  (c' = <{{ skip }}> -> terminal ac' /\ st' "b" = (if b' then 1 else 0) /\ st' = st'').
Proof.
  intros until ds. revert st ast c' st' ast' os. eapply prog_size_ind with (c:=ac) (ds:=ds).
  clear. intros until PA. intros Harrs Hunused st_b Hexec. destruct c; simpl in *.
  + invert Hexec; [|inversion H0]. eexists. exists <[ skip ]>, pc, P, PA. split; [|split; [constructor|tauto] ]. rewrite t_update_same. constructor.
  + invert Hexec; [solve_refl|]. invert H0. invert H1; [|inversion H0]. eexists. exists <[skip]>. do 3 eexists. rewrite t_update_neq; [|now invert Hunused]. split; [|split; [constructor|tauto] ].
    rewrite t_update_permute; [|now invert Hunused]. rewrite t_update_same. now repeat econstructor.
  + apply multi_spec_seq in Hexec. destruct Hexec.
    - destruct H0 as (?&?&?&?&?&?&?&->&->&?&?). apply spec_eval_preserves_nonempty_arrs in H0 as ?; [|tauto].
      invert Hunused. eapply H in H0; [|prog_size_auto|tauto..]. destruct H0 as (?&?&?&?&?&?&(?&?&->)); [tauto|].
      eapply H in H1; [|prog_size_auto|tauto..]. destruct H1 as (?&?&?&?&?&?&?). do 5 eexists. split; [|apply H7].
      eapply multi_ideal_unused_overwrite in H1; [|apply H4]. rewrite t_update_shadow in H1.
      eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H0|].
      rewrite <- app_nil_l with (l:=x3). rewrite <- app_nil_l with (l:=x5). econstructor; [|apply H1]. now constructor.
    - destruct H0 as (?&->&?). invert Hunused. eapply H in H0; [|prog_size_auto|tauto..]. destruct H0 as (?&?&?&?&?&?&?).
      do 5 eexists. split; [|discriminate]. apply multi_ideal_add_snd_com. apply H0.
  + invert Hexec; [solve_refl|]. invert H0.
    - destruct ((lbe || negb b'0) && beval st'0 be) eqn:Heq.
      * assert (beval st'0 (if lbe then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct b'0, (beval st'0 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H1.
        invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H2. invert H14. invert H3. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H1; [inversion H14|]. simpl in H2. rewrite H0, t_update_same in H2.
        eapply H in H2; [|prog_size_auto|tauto|now invert Hunused|tauto].
        destruct H2, H1, H1, H1, H1, H1. exists x, <[ branch pc x0 ]>. do 3 eexists. split; [|intro H'; apply H2 in H'; destruct H'; split; [now constructor|tauto] ].
        rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq; [reflexivity|]. apply multi_ideal_branch, H1.
      * assert (beval st'0 (if lbe then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct b'0, (beval st'0 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H1. invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H2. invert H14. invert H3. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H1; [inversion H14|]. simpl in H2. rewrite H0, t_update_same in H2.
        eapply H in H2; [|prog_size_auto|tauto|now invert Hunused|tauto].
        destruct H2, H1, H1, H1, H1, H1. exists x, <[branch pc x0]>. do 3 eexists. split; [|intro H'; apply H2 in H'; destruct H'; split; [now constructor|tauto] ].
        rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq; [tauto|apply multi_ideal_branch, H1].
    - destruct ((lbe || negb b) && beval st'0 be) eqn:Heq.
      * assert (beval st'0 (if lbe then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct b, (beval st'0 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H1. invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H2. invert H14. invert H3. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H1; [inversion H14|]. simpl in H2. rewrite H0 in H2.
        eapply H in H2; [|prog_size_auto|tauto|now invert Hunused|tauto].
        destruct H2, H1, H1, H1, H1, H1. rewrite t_update_eq in H1. eapply multi_ideal_unused_update in H1; [|now invert Hunused].
        exists x, <[branch pc x0]>. do 3 eexists. split; [|split; (destruct H2; [tauto|]); [now constructor|tauto] ]. rewrite !app_nil_l, H0.
        repeat econstructor; rewrite ?Heq; [tauto|apply multi_ideal_branch, H1].
      * assert (beval st'0 (if lbe then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct b, (beval st'0 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H1. invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H2. invert H14. invert H3. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H1; [inversion H14|]. simpl in H2. rewrite H0 in H2.
        eapply H in H2; [|prog_size_auto|tauto|now invert Hunused|tauto].
        destruct H2, H1, H1, H1, H1, H1. rewrite t_update_eq in H1. eapply multi_ideal_unused_update in H1; [|now invert Hunused].
        exists x, <[branch pc x0]>. do 3 eexists. split; [|split; (destruct H2; [tauto|]); [now constructor|tauto] ]. rewrite !app_nil_l, H0.
        repeat econstructor; rewrite ?Heq; [tauto|apply multi_ideal_branch, H1].
  + invert Hexec; [solve_refl|]. invert H0. invert H13. invert H1; [solve_refl|]. invert H0. invert H13.
    - destruct ((lbe || negb b'1) && beval st'1 be) eqn:Heq.
      * assert (beval st'1 (if lbe then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct b'1, (beval st'1 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H2. invert H2; [solve_refl|]. invert H1. invert H14. invert H13. invert H14. apply multi_spec_seq_assoc in H3. destruct H3, H1.
        invert H1. { do 5 eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate].
        do 2 econstructor; [reflexivity|constructor; [now rewrite H0, Heq|reflexivity] |simpl; rewrite t_update_same; constructor]. }
        invert H3. invert H15; [inversion H14|]. apply multi_spec_seq in H4. destruct H4.
        ++ do 8 destruct H1. destruct H3, H4. remember (if lbe then be else <{{ "b" = 0 && be }}>) as be'.
           replace <{{ while be' do "b" := be' ? "b" : 1; (flex_vslh_acom c) end; "b" := be' ? 1 : "b" }}> with (flex_vslh_acom <[ while be@lbe do c end ]>) in H5
             by now simpl; rewrite Heqbe'.
           subst. simpl in H4. rewrite H0, t_update_same in H4. eapply H in H4; [|prog_size_auto|tauto|now invert Hunused|tauto].
           destruct H4, H1, H1, H1, H1, H1, H3; [tauto|]. destruct H4. subst. eapply multi_ideal_preserves_nonempty_arrs in H1 as Harrs'; [|tauto].
           eapply H in H5; [|prog_size_auto|tauto|now invert Hunused|tauto]. destruct H5,H5, H5, H5, H5, H5. eapply multi_ideal_unused_overwrite in H5; [|eassumption].
           rewrite t_update_shadow in H5. exists x0, <[branch pc x12]>. do 3 eexists. split; [|intro Hc'; split; [constructor|]; tauto].
           do 2 econstructor; [reflexivity|constructor; rewrite H0, ?Heq; reflexivity|].
           simpl. apply multi_ideal_branch. eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H1|]. change x4 with ([] ++ x4). change x6 with ([] ++ x6).
           now econstructor; [apply ISM_Seq_Skip|eassumption].
        ++ do 2 destruct H1. subst. simpl in H3. rewrite H0, t_update_same in H3. eapply H in H3; [|prog_size_auto|tauto|now invert Hunused|tauto].
           destruct H3, H1, H1, H1, H1, H1. do 5 eexists. split; [|intro Habs; apply H2 in Habs; discriminate]. do 2 econstructor; [reflexivity|constructor; rewrite H0, ?Heq; reflexivity|].
           apply multi_ideal_branch. apply multi_ideal_add_snd_com, H1.
      * assert (beval st'1 (if lbe then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct b'1, (beval st'1 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H2. invert H2; [solve_refl|]. invert H1; [invert H14|]. invert H3; [solve_refl|]. invert H1. invert H2; [|inversion H1].
        do 5 eexists. split; [|split; [apply Terminal_Branch, Terminal_Skip|]; simpl; rewrite H0, t_update_eq, t_update_same; tauto]. rewrite t_update_same.
        do 2 econstructor; [constructor..|simpl; constructor]; now rewrite H0, ?Heq.
    - destruct ((lbe || negb b'0) && beval st'1 be) eqn:Heq.
      * assert (beval st'1 (if lbe then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct b'0, (beval st'1 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H2. invert H2; [solve_refl|]. invert H1; [invert H14|]. invert H3; [solve_refl|]. invert H1. invert H2; [|inversion H1].
        do 5 eexists. split; [|split; [apply Terminal_Branch, Terminal_Skip|]; simpl; rewrite H0, t_update_eq; tauto]. rewrite t_update_shadow, t_update_same.
        do 2 econstructor; [constructor..|simpl; constructor]; now rewrite H0, ?Heq.
      * assert (beval st'1 (if lbe then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct b'0, (beval st'1 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H2. invert H2; [solve_refl|]. invert H1. invert H14. invert H13. invert H14. apply multi_spec_seq_assoc in H3. destruct H3, H1.
        invert H1. { do 5 eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate].
        do 2 econstructor; [reflexivity|constructor; [now rewrite H0, Heq|reflexivity] |simpl; rewrite t_update_same; constructor]. }
        invert H3. invert H15; [inversion H14|]. apply multi_spec_seq in H4. destruct H4.
        ++ do 8 destruct H1. destruct H3, H4. remember (if lbe then be else <{{ "b" = 0 && be }}>) as be'.
           replace <{{ while be' do "b" := be' ? "b" : 1; (flex_vslh_acom c) end; "b" := be' ? 1 : "b" }}> with (flex_vslh_acom <[ while be@lbe do c end ]>) in H5
             by now simpl; rewrite Heqbe'.
           subst. simpl in H4. rewrite H0 in H4. eapply H in H4; [|prog_size_auto|tauto|now invert Hunused|tauto].
           destruct H4, H1, H1, H1, H1, H1, H3; [tauto|]. destruct H4. subst. eapply multi_ideal_preserves_nonempty_arrs in H1 as Harrs'; [|tauto].
           eapply H in H5; [|prog_size_auto|tauto|now invert Hunused|tauto]. destruct H5, H5, H5, H5, H5, H5. eapply multi_ideal_unused_overwrite in H5; [|eassumption].
           rewrite t_update_shadow in H5. exists x0, <[branch pc x12]>. do 3 eexists. split; [|intro Hc'; split; [constructor|]; tauto ]. do 2 econstructor; [reflexivity|constructor; rewrite H0, ?Heq; reflexivity|].
           simpl. rewrite t_update_eq in H1. eapply multi_ideal_unused_update in H1; [|now invert Hunused]. apply multi_ideal_branch.
           eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H1|]. change x4 with ([] ++ x4). change x6 with ([] ++ x6).
           econstructor; [apply ISM_Seq_Skip|]; eassumption.
        ++ do 2 destruct H1. subst. simpl in H3. rewrite H0 in H3. eapply H in H3; [|prog_size_auto|tauto|now invert Hunused|tauto].
           destruct H3, H1, H1, H1, H1, H1. do 5 eexists. split; [|intro Habs; apply H2 in Habs; discriminate]. do 2 econstructor; [reflexivity|constructor; rewrite H0, ?Heq; reflexivity|].
           rewrite t_update_eq in H1. apply multi_ideal_unused_update in H1; [|now invert Hunused]. apply multi_ideal_branch, multi_ideal_add_snd_com, H1.
  + destruct (lx&&li) eqn:Heq.
    - apply andb_prop in Heq. destruct Heq. subst.
      invert Hexec; [solve_refl|]. invert H0. invert H13.
      * invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; [tauto|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [constructor|now invert Hunused]. }
        invert H0; [inversion H13|]. invert H2. { do 5 eexists. split; [|discriminate]. rewrite app_nil_l. repeat econstructor; [tauto|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [constructor|now invert Hunused]. }
        invert H0. invert H1; [|inversion H0]. rewrite t_update_shadow. rewrite t_update_neq; [|now invert Hunused].
        do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite !app_nil_l. repeat econstructor; [tauto|]. simpl. rewrite t_update_neq; [|now invert Hunused].
        rewrite t_update_permute; [|now invert Hunused]. rewrite t_update_same, t_update_eq, st_b. now destruct b'; constructor.
      * invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; [tauto..|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [|now invert Hunused]. constructor. }
        invert H0; [inversion H13|]. invert H2. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; [tauto..|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [constructor|now invert Hunused]. }
        invert H0. invert H1; [|inversion H0]. rewrite t_update_shadow. rewrite t_update_neq; [|now invert Hunused].
        do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite !app_nil_l. repeat econstructor; [tauto..|]. rewrite t_update_permute; [|now invert Hunused].
        rewrite t_update_same. simpl. rewrite t_update_neq; [|now invert Hunused]. rewrite st_b. constructor.
    - invert Hexec; [solve_refl|]. invert H0.
      * invert H1; [|inversion H0]. rewrite t_update_neq; [|now invert Hunused]. do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ].
        repeat econstructor; [|tauto|]. { destruct lx, li, b'; simpl in *; rewrite ?st_b; try reflexivity; discriminate. }
        rewrite t_update_permute; [|now invert Hunused]. rewrite t_update_same. destruct li, lx, b'; simpl; rewrite ?st_b; try constructor; discriminate.
      * invert H1; [|inversion H0]. do 5 eexists. rewrite t_update_neq; [|now invert Hunused]. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite t_update_permute; [|now invert Hunused].
        rewrite t_update_same. repeat econstructor. destruct li; [repeat constructor; rewrite andb_true_r in Heq; subst; tauto|].
        simpl in H15. rewrite st_b in H15. simpl in H15. specialize (Harrs a). lia.
  + invert Hexec; [solve_refl|]. invert H0.
    - invert H1; [|inversion H0]. do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite t_update_same. repeat econstructor; [|tauto].
      now destruct b', li; simpl; rewrite ?st_b.
    - invert H1; [|inversion H0]. do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite t_update_same. destruct li; [now repeat econstructor|].
      simpl in H16. rewrite st_b in H16. simpl in H16. specialize (Harrs a). lia.
  + eapply H in Hexec; [|prog_size_auto|tauto..]. destruct Hexec as (st''&ac'&?&?&?&?&?). exists st'', <[branch lbl ac']>. do 3 eexists. split; [|split; [constructor|]; tauto].
    apply multi_ideal_branch. eassumption.
Qed.

Lemma flex_slh_acom_bcc : forall ac st ast c' st' ast' os ds (b b' : bool) pc P PA,
  nonempty_arrs ast ->
  acom_unused "b" ac ->
  st "b" = (if b then 1 else 0) ->
  <((flex_vslh_acom ac, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists st'' ac' pc' P' PA',
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ac', "b" !-> st "b"; st'', ast', b', pc', P', PA']]>.
Proof. intros. eapply flex_slh_acom_bcc_generalized in H2; [|tauto..]. destruct H2 as (st''&ac'&?&?&?&?&?). now eauto 20. Qed.

Lemma static_tracking_no_branch : forall c P PA P' PA' pc ac lbl,
  static_tracking c P PA pc = (<[branch lbl ac]>, P', PA') ->
  False.
Proof.
  induction c; simpl; intros; invert H.
  + destruct (static_tracking c1 P PA pc) as ((ac1&P1)&PA1), (static_tracking c2 P1 PA1 pc) as ((ac2&P2)&PA2).
    invert H1.
  + destruct (static_tracking c1 P PA (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1), (static_tracking c2 P PA (join pc (label_of_bexp P be))) as ((ac2&P2)&PA2).
    invert H1.
  + destruct (static_tracking_while (static_tracking c) P PA pc
         (length (assigned_vars c) + length (assigned_arrs c)) be
         (assigned_vars c) (assigned_arrs c) (filter P (assigned_vars c)) (filter PA (assigned_arrs c))) as (((P1&PA1)&lbe)&ac1).
    invert H1.
Qed.


(* LD: This has to be rephrased *)
Lemma ideal_misspeculated_unwinding_one_step : forall P PA P' PA' pc ac c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds
    pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  static_tracking c P PA pc = (ac, P', PA') ->
  pub_equiv P st1 st2 ->
  <[[ac, st1, ast1, true, pc, P, PA]]> -->i_ds^^os1 <[[ct1, stt1, astt1, true, pct1, Pt1, PAt1]]> ->
  <[[ac, st2, ast2, true, pc, P, PA]]> -->i_ds^^os2 <[[ct2, stt2, astt2, true, pct2, Pt2, PAt2]]> ->
  os1 = os2 /\ ct1 = ct2.
Proof.
(*
  intros. apply erase_static_tracking in H as H'. subst.
  remember true as b in H1 at 1. remember true as bt in H1. revert st2 ast2 os2 ct2 stt2 astt2 P' PA' pct2 Pt2 PAt2 H H0 H2 Heqb Heqbt.
  induction H1; simpl; intros.
  + now invert H2.
  + destruct (static_tracking (erase c1) P PA pc) as ((ac1&P1)&PA1) eqn:Heq1.
    destruct (static_tracking (erase c2) P1 PA1 pc) as ((ac2&P2)&PA2) eqn:Heq2. invert H. invert H2; [|now apply ideal_terminal_no_step in H1].
    eapply IHideal_eval_small_step in H19; [|now eauto..]. now invert H19.
  + invert H2; [now apply ideal_terminal_no_step in H20|tauto].
  + invert H3. destruct (static_tracking (erase ct) Pt2 PAt2 (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1).
    destruct (static_tracking (erase cf) P PA (join pc (label_of_bexp P be))) as ((ac2&P2)&PA2).
    invert H1. destruct (label_of_bexp P be) eqn:Heq; [|tauto]. erewrite noninterferent_bexp; [tauto|eassumption|].
    unfold public. rewrite <- Heq. apply label_of_exp_sound.
  + invert H3.
    destruct (static_tracking (erase ct) P PA (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1).
    destruct (static_tracking (erase cf) P PA (join pc (label_of_bexp P be))) as ((ac2&P2)&PA2). invert H1.
    destruct (label_of_bexp P be) eqn:Heq; [|tauto]. erewrite noninterferent_bexp; [tauto|eassumption|].
    unfold public. rewrite <- Heq. apply label_of_exp_sound.
  + now invert H2.
  + invert H4. invert H2. destruct (label_of_aexp P ie) eqn:Heq; [|tauto]. erewrite noninterferent_aexp; [now eauto..|].
    unfold public. rewrite <- Heq. apply label_of_exp_sound.
  + invert H5. invert H3. erewrite noninterferent_aexp; [now eauto..|]. rewrite <- H5. apply label_of_exp_sound.
  + invert H5. invert H3. destruct (label_of_aexp P' ie) eqn:Heq; [|tauto]. erewrite noninterferent_aexp; [now eauto..|].
    unfold public. rewrite <- Heq. apply label_of_exp_sound.
  + invert H5. invert H3. erewrite noninterferent_aexp; [now eauto..|]. rewrite <- H0. apply label_of_exp_sound.
  + invert H2. now apply static_tracking_no_branch in H.
Admitted.

Lemma ideal_misspeculated_unwinding : forall P PA P' PA' pc ac c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds,
  static_tracking c P PA pc = (ac, P', PA') ->
  pub_equiv P st1 st2 ->
  <[[ac, st1, ast1, true]]> -->i*_ds^^os1 <[[ct1, stt1, astt1, true]]> ->
  <[[ac, st2, ast2, true]]> -->i*_ds^^os2 <[[ct2, stt2, astt2, true]]> ->
  os1 = os2.
Proof.
*)
Admitted.

Lemma fs_flex_vsls_correct_small_step : forall P PA c c' st ast st' ast' os,
  st "b" = 0 ->
  unused "b" c ->
  <(( c, st, ast ))> -->^ os <((c', st', ast'))> ->
  exists c'',
  <((fs_flex_vslh P PA c, st, ast))> -->*^ os <((c'', st', ast'))> /\ (c' = <{ skip }> -> c'' = <{ skip }>).
Proof.
(*
  intros until os. intros st_b Hunused H. revert Hunused. induction H; unfold fs_flex_vslh in *; simpl; intro Hunused.
  + eexists. split; [rewrite <- app_nil_l; repeat econstructor|reflexivity].
    rewrite H. constructor.
  + destruct IHseq_eval_small_step as (c''&?&?); [tauto..|]. destruct (static_tracking c1 P PA public) as ((ac&P1)&PA1) eqn:Heq.
    destruct (static_tracking c2 P1 PA1 public) as ((ac'&P2)&PA2) eqn:Heq'. simpl.
    eexists. split; [|discriminate]. apply multi_seq_add_snd_com, H0.
  + destruct (static_tracking c2 P PA public) as ((ac&P')&PA') eqn:Heq.
    eexists. simpl. change [] with ([] ++ [] : obs). split; [eapply multi_seq_trans; [apply SSM_Seq_Skip|constructor]|].
    intros ->. simpl in Heq. now invert Heq.
  + destruct (static_tracking ct P PA (label_of_bexp P be)) as ((ac1&P1)&PA1) eqn:Heq1.
    destruct (static_tracking cf P PA (label_of_bexp P be)) as ((ac2&P2)&PA2) eqn:Heq2.
    simpl. destruct (label_of_bexp P be) eqn:Heq.
    - exists (if beval st be then flex_vslh_acom ac1 else flex_vslh_acom ac2).
      split; [|now destruct (beval st be); intros ->; [invert Heq1|invert Heq2] ].
      simpl. change [_] with ([OBranch (beval st be)] ++ [] ++ [] ++ []).
      econstructor; [constructor|]. destruct (beval st be) eqn:Hbe; (do 2 econstructor; [now constructor; simpl; rewrite Hbe|apply SSM_Seq_Skip|rewrite t_update_same; constructor]).
    - exists (if beval st be then flex_vslh_acom ac1 else flex_vslh_acom ac2).
      split; [|now destruct (beval st be); intros ->; [invert Heq1|invert Heq2] ].
      simpl. change [_] with ([OBranch (beval st be)] ++ [] ++ [] ++ []).
      replace (beval st be) with (beval st <{{ "b" = 0 && be }}>) by now (simpl; rewrite ?st_b).
      econstructor; [constructor|].
      destruct (beval st <{{ "b" = 0 && be }}>) eqn:Hbe; (do 2 econstructor; [now constructor; simpl in *; rewrite Hbe|apply SSM_Seq_Skip|rewrite t_update_same; constructor]).
  + destruct (static_tracking_while (static_tracking c) P PA public (length (assigned_vars c) + length (assigned_arrs c)) be (assigned_vars c) 
       (assigned_arrs c) (filter P (assigned_vars c)) (filter PA (assigned_arrs c))) as (((?&?)&?)&?).
    eexists. split; [constructor|discriminate].
  + eexists. split; [|reflexivity]. destruct (join (label_of_aexp P ie) (PA a) && label_of_aexp P ie).
    - change [_] with ([OARead a i] ++ [] ++ [] ++ []).
      econstructor; [now repeat econstructor|]. econstructor; [apply SSM_Seq_Skip|]. econstructor; [|constructor].
      remember (x !-> _; st) as st'.
      replace st' with (x !-> aeval st' <{ ("b" = 1) ? 0 : x }>; st') at 2
        by now rewrite Heqst'; simpl; rewrite t_update_neq; [|tauto]; rewrite st_b, t_update_same.
      now constructor.
    - rewrite <- app_nil_r. repeat econstructor; [|tauto].
      now destruct (label_of_aexp P ie && negb (join (label_of_aexp P ie) (PA a))); simpl; rewrite ?st_b.
  + eexists. split; [|reflexivity].
    rewrite <- app_nil_r. repeat econstructor; [|tauto|rewrite H; constructor].
    now destruct (label_of_aexp P ie); simpl; rewrite ?st_b.
*)
Admitted.

Lemma seq_unused : forall X c st ast c' st' ast' os,
  <((c, st, ast))> -->^os <((c', st', ast'))> ->
  unused X c ->
  unused X c' /\ st' X = st X.
Proof.
  intros. revert H0. induction H; simpl; intro; rewrite ?t_update_neq; try tauto.
  destruct (beval st be); tauto.
Qed.

(* LD: This kind of theorem would be nice to have...
       The one step version isn't strong enough as it is stated though *)
Theorem fs_flex_vslh_correct : forall P PA c c' st ast st' ast' os,
  st "b" = 0 ->
  unused "b" c ->
  <(( c, st, ast ))> -->*^ os <((c', st', ast'))> ->
  exists c'',
  <((fs_flex_vslh P PA c, st, ast))> -->*^ os <((c'', st', ast'))>.
Proof.
Admitted.

Lemma multi_ideal_no_spec_deterministic : forall c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 ds os1 os2
    pc P PA pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  seq_same_obs (erase c) st1 st2 ast1 ast2 ->
  <[[c, st1, ast1, false, pc, P, PA]]> -->i*_ds^^os1 <[[ct1, stt1, astt1, false, pct1, Pt1, PAt1]]> ->
  <[[c, st2, ast2, false, pc, P, PA]]> -->i*_ds^^os2 <[[ct2, stt2, astt2, false, pct2, Pt2, PAt2]]> ->
  os1 = os2.
Proof.
  intros. apply multi_ideal_no_spec in H0 as Heq.
  destruct Heq as (n&->). apply multi_ideal_obs_length in H0 as Heq, H1 as Heq'.
  rewrite Heq' in Heq. clear Heq'. apply multi_ideal_multi_seq in H1, H0.
  apply prefix_eq_length; [now symmetry|]. eapply H; eassumption.
Qed.

Lemma multi_ideal_misspeculate_split : forall ds c st ast ct stt astt os pc pct P Pt PA PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, true, pct, Pt, PAt]]> ->
  exists n ds2 os1 o os2 c1 c2 st1 st2 ast1 ast2 pc1 pc2 P1 P2 PA1 PA2,
  ds = repeat DStep n ++ DForce :: ds2 /\
  os = os1 ++ o :: os2 /\
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ repeat DStep n ^^os1 <[[c1, st1, ast1, false, pc1, P1, PA1]]> /\
  <[[c1, st1, ast1, false, pc1, P1, PA1]]> -->i_[DForce]^^[o] <[[c2, st2, ast2, true, pc2, P2, PA2]]> /\
  <[[c2, st2, ast2, true, pc2, P2, PA2]]> -->i*_ds2^^os2 <[[ct, stt, astt, true, pct, Pt, PAt]]>.
Proof.
  induction ds; intros; [now apply multi_ideal_spec_needs_force in H|].
  apply multi_ideal_factorize in H. do 13 destruct H. destruct H0, H1. subst.
  destruct x4.
  + apply ideal_eval_small_step_spec_needs_force in H1 as Heq. invert Heq.
    change (DForce :: ds) with ([]++[DForce]++ds). change (x5::x6) with ([]++ x5 :: x6).
    exists 0, ds. now eauto 20.
  + apply IHds in H2. destruct H2. do 17 destruct H. destruct H2, H3. subst.
    apply ideal_eval_small_step_no_spec in H1 as Heq. destruct Heq; [|discriminate]. invert H.
    eapply multi_ideal_trans in H1; [|eassumption]. eapply multi_ideal_combined_executions in H1; [|eassumption].
    rewrite !app_comm_cons. exists (1+x4), x11. now eauto 20.
Qed.

Lemma ideal_eval_small_step_force_obs : forall c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 os1 os2
    pc P PA pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  seq_same_obs (erase c) st1 st2 ast1 ast2 ->
  <[[c, st1, ast1, false, pc, P, PA]]> -->i_[DForce]^^os1 <[[ct1, stt1, astt1, true, pct1, Pt1, PAt1]]> ->
  <[[c, st2, ast2, false, pc, P, PA]]> -->i_[DForce]^^os2 <[[ct2, stt2, astt2, true, pct2, Pt2, PAt2]]> ->
  os1 = os2.
Proof.
  intros. remember false as b in H0. remember true as bt in H0. remember [DForce] as ds in H0.
  revert st2 ast2 os2 ct2 stt2 astt2 Heqb Heqbt Heqds H H1. induction H0; intros; subst; try discriminate.
  + invert H1. apply seq_same_obs_com_seq in H. eapply IHideal_eval_small_step; [tauto..|eassumption|eassumption].
  + invert H2. apply seq_same_obs_com_if in H1. now rewrite H1, !orb_true_r.
  + invert H1. eapply IHideal_eval_small_step; eauto.
Qed.

(* LD: Add a way to know that ac comes is created from P PA for which the states are equivalent *)
(* CH: You could add something like this (and potentially use c instead of `erase ac`
       in the premise, although your theorems will probably anyway say it's all the same):
  static_tracking c P PA public = (ac, P', PA') ->
  pub_equiv P st st' ->
  pub_equiv PA ast ast' ->
It will probably be very similar to the main theorem statement below?
       In particular, can't you use fs_flex_vslh in the conclusion instead of erased in the premise? *)
Theorem ideal_eval_relative_secure : forall ac c st st' ast ast' P PA P' PA',
  static_tracking c P PA public = (ac, P', PA') ->
  pub_equiv P st st' ->
  pub_equiv PA ast ast' ->
  nonempty_arrs ast ->
  nonempty_arrs ast' ->
  seq_same_obs c st st' ast ast' ->
  ideal_same_obs ac st st' ast ast' P PA.
Proof.
  unfold ideal_same_obs. intros. eapply multi_ideal_spec_bit_deterministic in H5 as Heq; [|eassumption]. subst.
  apply erase_static_tracking in H as H'. subst.
  destruct b1; [|eapply multi_ideal_no_spec_deterministic; eassumption].
  apply multi_ideal_misspeculate_split in H5, H6.
  destruct H5 as (n1&ds1&os1'&o1&os1''&c1&c1'&st1&st1'&ast1&ast1'&?&?&?&?&?&?&->&->&?&?&?).
  destruct H6 as (n2&ds2&os2'&o2&os2''&c2&c2'&st2&st2'&ast2&ast2'&?&?&?&?&?&?&?&->&?&?&?).
  apply repeat_same_length in H6 as H'; [|discriminate]. subst. apply app_inv_head in H6. invert H6.
  eapply multi_ideal_no_spec_deterministic in H9 as Heq; [|eassumption..]. subst. f_equal.
  apply multi_ideal_multi_seq in H5, H9. assert (c1 = c2) by admit. subst.
  eapply multi_seq_preserves_seq_same_obs in H9 as Hobs; [|apply H5|eassumption|reflexivity].
Admitted.

(* LD: Does not rely on pub_equiv right now, probably something wrong in the other statements *)
(* CH: I agree that these pub_equiv conditions seem also needed above *)
Theorem fs_flex_vslh_relative_secure : forall P PA c st ast st' ast',
  unused "b" c ->
  st "b" = 0 ->
  st' "b" = 0 ->
  pub_equiv P st st' ->
  pub_equiv PA ast ast' ->
  nonempty_arrs ast ->
  nonempty_arrs ast' ->
  seq_same_obs c st st' ast ast' ->
  spec_same_obs (fs_flex_vslh P PA c) st st' ast ast'.
Proof.
  unfold spec_same_obs, fs_flex_vslh. intros.
  destruct (static_tracking c P PA public) as ((ac&P')&PA') eqn:Heq.
  eapply flex_slh_acom_bcc in H7; try tauto; [|unfold acom_unused; erewrite erase_static_tracking; eassumption].
  eapply flex_slh_acom_bcc in H8; try tauto; [|unfold acom_unused; erewrite erase_static_tracking; eassumption].
  destruct H7 as (st1''&ac1'&?&?&?&?), H8 as (st2''&ac2'&?&?&?&?).
  eapply ideal_eval_relative_secure; eassumption.
Qed.

(* CH: My advice would be to also look at the 2 other conjectures I tested
   at the very end of TestingFlexSLH.v and turn that into noninterference and
   ideal_misspeculated_unwinding lemmas in the proofs. *)

