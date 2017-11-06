Require Import String ListSet CpdtTactics ListSet Wf String.
Require Import OpalSrc.OpalUtil.

Set Implicit Arguments.
Open Scope string_scope.

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

Definition var := string.
Definition node := string.
Definition world := string.
Definition op := string.

Inductive sexp :=
| EmptySet : sexp
| Var      : node -> var -> sexp
| Cons     : sexp -> sexp -> sexp.

Inductive sexp_is_value : sexp -> Prop :=
| EmptySetIsValue : sexp_is_value EmptySet
| ConsValuesIsValue : forall s1 s2,
    sexp_is_value s1 -> sexp_is_value s2 -> sexp_is_value (Cons s1 s2).
Hint Constructors sexp_is_value.

Definition is_sexp_value : forall s, {sexp_is_value s} + {~sexp_is_value s}.
Proof.
  induction s.
  * left. auto.
  * right. unfold not. intros. inversion H.
  * destruct IHs1; destruct IHs2.
    - auto.
    - right. unfold not. intros. inversion H. contradiction H3.
    - right. unfold not. intros. inversion H. contradiction H2.
    - right. unfold not. intros. inversion H. contradiction H2.
Qed.

Definition sexp_value := {sexp | sexp_is_value sexp}.

Inductive bool :=
| Eq    : sexp -> sexp -> bool
| Mem   : sexp -> sexp -> bool
| Conj  : bool -> bool -> bool
| Disj  : bool -> bool -> bool
| True  : bool
| False : bool.

Inductive bool_is_value : bool -> Prop :=
| TrueIsValue : bool_is_value True
| FalseIsValue : bool_is_value False
.
Definition bool_value := { b: bool | bool_is_value b}.

Inductive com :=
| Skip   : com
| Seq    : com -> com -> com
| If     : bool -> com -> com -> com
| With   : node -> com -> com
| At     : node -> com -> com
| Hyp    : world -> com -> com
| Commit : world -> com
| Handle : node -> var -> op -> sexp -> sexp -> com -> com
| Op     : op -> com.

Definition var_store := StringPairMap.t sexp_value.
Definition var_store_stack := list var_store.
Definition world_store := world -> option (var_store_stack * var_store).
Definition principals := set node.
Definition location := node.
Definition handlers := op -> option (node * var * sexp).
Definition mergers := node -> var -> option sexp.

Inductive error :=
| GenericErr : string -> error
| LookupErr  : node -> var -> error
| ReadPermErr : node -> var -> principals -> error
| WritePermErr : node -> var -> principals -> error
| MergeErr : node -> var -> mergers -> error
| HandleErr : op -> handlers -> error
| BoolEvalErr : bool -> error
| CommitErr : world -> world_store -> error
.

Definition empty_env : var_store := StringPairMap.empty sexp_value.

Definition set_env (e: var_store) (n: node) (v: var) (val: sexp_value) : var_store :=
  StringPairMap.add (n, v) val e.

Definition get_env (e: var_store) (n: node) (v: var) : option sexp_value :=
  StringPairMap.find (n, v) e.

Fixpoint lookup (n: node) (v: var) (Sigma: var_store_stack)
  : (sexp_value + error) :=
  match Sigma with
  | nil => inr (LookupErr n v)
  | cons e rest =>
    match get_env e n v with
    | Some res => inl res
    | None => lookup n v rest
    end
  end.

Definition empty_world_store : world_store :=
  fun _ => None.

Definition set_world_store (w: world_store) (u: world) (S: var_store_stack) (s: var_store) : world_store :=
  fun u' =>
    match string_dec u u' with
    | left _ => Some (S, s)
    | right _ => w u'
    end.

Definition empty_handlers : handlers :=
  fun _ => None.

Definition set_handler (h: handlers) (o: op) (n: node) (v: var) (s: sexp) : handlers :=
  fun o' =>
    match string_dec o o' with
    | left _ => Some (n, v, s)
    | right _ => h o'
    end.

Definition empty_mergers : mergers :=
  fun _ _ => None.

Definition set_merger (m: mergers) (n: node) (v: var) (s: sexp) : mergers :=
  fun n' v' =>
    match (string_dec n n', string_dec v v') with
    | (left _, left _) => Some s
    | _ => m n' v'
    end.

Fixpoint sexp_step (s: sexp) (Sigma: var_store_stack) (pi: principals)
  : (sexp_value + error) :=
  match s with
  | EmptySet => inl (exist sexp_is_value EmptySet EmptySetIsValue)
  | Cons l r =>
    match (sexp_step l Sigma pi), (sexp_step r Sigma pi) with
    | inl (exist _ lv Hl), inl (exist _ rv Hr) =>
      inl (exist _ (Cons lv rv) (ConsValuesIsValue Hl Hr))
    | inr err, _ => inr err
    | _, inr err => inr err
    end
  | Var n v =>
    match set_mem string_dec n pi with
    | true => lookup n v Sigma
    | false => inr (ReadPermErr n v pi)
    end
  end.

Lemma canonical_sexp_value :
  forall v Sigma pi H,
    sexp_step v Sigma pi = inl (exist sexp_is_value v H).
Proof.
  induction v ; intros.
  * specialize proof_irrelevance with (sexp_is_value EmptySet) EmptySetIsValue H.
    crush.
  * inversion H.
  * inversion H.
    specialize IHv1 with Sigma pi H2.
    specialize IHv2 with Sigma pi H3.
    specialize proof_irrelevance with (sexp_is_value (Cons v1 v2))
                                      (ConsValuesIsValue H2 H3) H.
    crush.
Qed.

Lemma canonical_sexp_cons :
  forall v l r Sigma pi H,
  sexp_is_value v ->
  sexp_step v Sigma pi = inl (exist sexp_is_value (Cons l r) H) ->
  v = (Cons l r).
Proof.
  intros.
  induction v.
  * unfold sexp_step in H0.
    fold sexp_step in H0.
    destruct (sexp_step l Sigma pi).
  - destruct s.
    destruct (sexp_step r Sigma pi).
    + destruct s0. crush.
    + discriminate.
  - discriminate.
  * inversion H0.
  * inversion H0.
    specialize canonical_sexp_value with v1 Sigma pi H4.
    specialize canonical_sexp_value with v2 Sigma pi H5.
    intros.
    subst.
    unfold sexp_step in H1.
    fold sexp_step in H1.
    destruct (sexp_step v1 Sigma pi) ;
      destruct (sexp_step v2 Sigma pi) ;
      try (destruct s;
           destruct s0);
      crush.
Qed.



Lemma canonical_sexp_value_2 :
  forall v v' Sigma pi H,
    sexp_is_value v ->
    sexp_step v Sigma pi = inl (exist sexp_is_value v' H) ->
    v = v'.
Proof.
  induction v ; intros.
  * crush.
  * inversion H0.
  * inversion H0.
    subst.
    inversion H1.
    destruct (sexp_step v1 Sigma pi) eqn:?.
    - destruct s.
      destruct (sexp_step v2 Sigma pi) eqn:?.
      + destruct s0.
        specialize IHv1 with x Sigma pi s.
        specialize IHv2 with x0 Sigma pi s0.
        crush.
      + crush.
    - crush.
Qed.

Inductive bool_lt : bool -> bool -> Prop :=
| ValueLt : forall b1 b2,
    bool_is_value b1 ->
    ~ bool_is_value b2 ->
    bool_lt b1 b2
| SexpValueLtEqL : forall s1 s2 s3,
    sexp_is_value s1 ->
    ~sexp_is_value s2 ->
    bool_lt (Eq s1 s3) (Eq s2 s3)
| SexpValueLtEqR : forall s1 s2 s3,
    sexp_is_value s1 ->
    ~sexp_is_value s2 ->
    bool_lt (Eq s3 s1) (Eq s3 s2)
| SexpValueLtMemL : forall s1 s2 s3,
    sexp_is_value s1 ->
    ~sexp_is_value s2 ->
    bool_lt (Mem s1 s3) (Mem s2 s3)
| SexpValueLtMemR : forall s1 s2 s3,
    sexp_is_value s1 ->
    ~sexp_is_value s2 ->
    bool_lt (Mem s3 s1) (Mem s3 s2)
| ConjLtL : forall b1 b2,
    bool_lt b1 (Conj b1 b2)
| ConjLtR : forall b1 b2,
    bool_lt b2 (Conj b1 b2)
| DisjLtL : forall b1 b2,
    bool_lt b1 (Disj b1 b2)
| DisjLtR : forall b1 b2,
    bool_lt b2 (Disj b1 b2)
| EqLt : forall ll lr rl rr,
    sexp_is_value ll ->
    sexp_is_value lr ->
    sexp_is_value rl ->
    sexp_is_value rr ->
    bool_lt (Conj (Eq ll rl) (Eq lr rr)) (Eq (Cons ll lr) (Cons rl rr))
| MemLt : forall l rl rr,
    sexp_is_value l ->
    sexp_is_value rl ->
    sexp_is_value rr ->
    bool_lt (Disj (Eq l rl) (Mem l rr)) (Mem l (Cons rl rr))
.

Lemma acc_true : Acc bool_lt True.
Proof.
  constructor ;
  intros ;
  inversion H ;
  contradiction H1 ;
  constructor.
Qed.

Lemma acc_false : Acc bool_lt False.
Proof.
  constructor ;
  intros ;
  inversion H ;
  contradiction H1 ;
  constructor.
Qed.

Lemma acc_eq_val : forall s1 s2,
    sexp_is_value s1 ->
    sexp_is_value s2 ->
    Acc bool_lt (Eq s1 s2).
Proof.
  Hint Constructors bool_is_value sexp_is_value.
  Hint Resolve acc_true acc_false.
  Ltac DKill y H1 H2 H3 H4 :=
    constructor ;
    intros ;
    destruct y ;
    inversion H1 ;
    inversion H2 ;
    inversion H3 ;
    try (solve [contradiction H4]) ;
    auto.

  induction s1 ; induction s2 ; intros ;
    try (solve [ DKill y H H1 H2 H7
               | inversion H ;
                 DKill y H5 H5 H6 H11
        ]).
  * intros.
    inversion H.
    inversion H0.
    specialize (IHs1_1 s2_1 H3 H7).
    specialize (IHs1_2 s2_2 H4 H8).
    constructor.
    intros.
    destruct y ; inversion H9;
      try (solve [inversion H10]) ;
      try (solve [contradiction H15]) ;
      auto.
    subst.
    constructor.
    intros.
    destruct y ; inversion H1;
      try (solve [inversion H2]) ; auto.
Qed.

Lemma acc_eq : forall s1 s2, Acc bool_lt (Eq s1 s2).
Proof.
  Hint Constructors bool_is_value sexp_is_value.
  Hint Resolve acc_true acc_false acc_eq_val.
  induction s1 ; induction s2 ; auto.
  * constructor ; intros. destruct y ; inversion H ;
      try (solve [inversion H0]) ;
      try (solve [contradiction H5 ; constructor]);
      auto.
  * constructor ; intros. destruct y ; inversion H ;
      try (solve [inversion H0]) ;
      try (solve [contradiction H5 ; constructor]);
      auto.
  * constructor ; intros. destruct y ; inversion H ;
      try (solve [inversion H0]) ;
      try (solve [contradiction H5 ; constructor]);
      auto.
  * constructor ; intros. destruct y ; inversion H.
    - inversion H0.
    - destruct s ; inversion H.
      + inversion H6.
      + subst.
        inversion H.
        ** inversion H0.
        ** subst.
           constructor.
           intros.
           destruct y ; inversion H0;
             auto ;
             inversion H1;
             contradiction H13.
      + inversion H6.
      + inversion H9.
      + subst. inversion H9.
      + inversion H6.
      + subst.
        inversion H.
        ** inversion H0.
        ** subst.
           constructor.
           intros.
           destruct y ; inversion H0;
             auto ;
             inversion H1;
             contradiction H13.
    - subst.
      destruct s0 ; inversion H.
      + inversion H0.
      + constructor.
        intros.
        destruct y ; inversion H7;
          auto;
          inversion H8 ;
          contradiction H13.
      + inversion H0.
      + inversion H4.
      + inversion H4.
      + inversion H0.
      + constructor.
        intros.
        destruct y ; inversion H7;
          auto;
          inversion H8 ;
          contradiction H13.
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - auto.
    - auto.

  * constructor ; intros. destruct y ; inversion H.
    - inversion H0.
    - destruct s ; inversion H.
      + inversion H6.
      + subst.
        inversion H.
        ** inversion H0.
        ** subst.
           constructor.
           intros.
           destruct y ; inversion H0;
             auto ;
             inversion H1;
             contradiction H13.
      + inversion H6.
      + inversion H9.
      + inversion H3.
      + inversion H6.
      + subst.
        inversion H.
        ** inversion H0.
        ** subst.
           constructor.
           intros.
           destruct y ; inversion H0 ; auto.
           -- inversion H1.
           -- contradiction H13.
           -- inversion H1.
           -- inversion H1.
           -- subst.
              constructor.
              intros.
              destruct y ; inversion H1 ; auto ; try (inversion H2).
           -- inversion H1.
    - subst.
      constructor.
      intros.
      destruct y ; inversion H0 ; inversion H1; auto. contradiction H8.
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - auto.
    - auto.
 * subst.
   constructor.
   intros.
   destruct y ; inversion H ; auto; inversion H0 ; contradiction H5; auto.
 * constructor.
   intros.
   destruct y ; inversion H ;auto; inversion H0 ; try (solve [contradiction H5]); auto.
   - subst.
constructor.
   intros.
   destruct y ; inversion H0 ; auto; inversion H1. contradiction H9.
   - subst.
     constructor.
     intros.
     destruct y ; inversion H0 ; auto; inversion H1. contradiction H9.
     subst.
     constructor.
     intros.
     destruct y ; inversion H1; auto ; inversion H2.
  *
    constructor.
    intros.
    destruct y ; inversion H ; auto ; inversion H0.
   - subst.
     constructor. intros.
     destruct y ; inversion H0 ; auto ; inversion H1. contradiction H9.
     subst.
     constructor. intros.
     destruct y ; inversion H1 ; auto ; inversion H2.
   - subst.
     constructor. intros.
     destruct y ; inversion H0 ; auto ; inversion H1. contradiction H9.
     subst.
     constructor. intros.
     destruct y ; inversion H1 ; auto ; inversion H2.
   - subst.
     constructor. intros.
     destruct y ; inversion H0 ; auto ; inversion H1.
Qed.

Lemma acc_mem_val : forall s1 s2,
    sexp_is_value s1 ->
    sexp_is_value s2 ->
    Acc bool_lt (Mem s1 s2).
Proof.
  Hint Constructors bool_is_value sexp_is_value.
  Hint Resolve acc_true acc_false.
  induction s2 ; intros ;
    try (solve [ DKill y H H1 H2 H7
               | inversion H ;
                 DKill y H5 H5 H6 H11
        ]).
  * constructor.
    intros.
    destruct y ; inversion H1; auto ; inversion H2.
    - constructor.
      intros.
      destruct y ; inversion H0; auto.
      + subst.
        inversion H9. inversion H2.
      + inversion H9.
        ** subst. inversion H10.
        ** subst. contradiction H15.
        ** subst. contradiction H15.
      + inversion H9.
        ** subst. inversion H10.
      + inversion H9.
        ** subst. inversion H10.
    -contradiction H7.
  * inversion H0.
  * constructor.
    intros.
    destruct y ; inversion H1; auto; inversion H2 ; try (solve [contradiction H7]).
    subst.
    constructor.
    intros.
    destruct y ; inversion H2; auto ; inversion H3 ; try (solve [contradiction H7]).
Qed.

Lemma acc_mem : forall s2 s1, Acc bool_lt (Mem s1 s2).
Proof.
  Hint Constructors bool_is_value sexp_is_value.
  Hint Resolve acc_true acc_false acc_eq_val acc_eq acc_mem_val.
  induction s2; intros.
  * constructor. intros.
    destruct y ; inversion H; auto ; inversion H0. contradiction H5. auto.
  * constructor. intros.
    destruct y ; inversion H; auto ; inversion H0.
  - constructor. intros.
    destruct y ; inversion H7; auto ; inversion H8. contradiction H13.
  - constructor. intros.
    destruct y ; inversion H7; auto ; inversion H8. contradiction H13.
    subst.
    constructor. intros.
    destruct y ; inversion H0; auto ; inversion H1.
  * constructor.
    intros.
    destruct y ; inversion H; auto ; inversion H0 ; subst.
    - constructor.
      intros.
      destruct y ; inversion H0 ; auto ; inversion H1. contradiction H9.
      subst.
      constructor.
      intros.
      destruct y ; inversion H1 ; auto ; inversion H2.
    - constructor.
      intros.
      destruct y ; inversion H0 ; auto ; inversion H1. contradiction H9.
      constructor.
      intros.
      destruct y ; inversion H12 ; auto ; inversion H13.
    - constructor.
      intros.
      destruct y ; inversion H0 ; auto ; inversion H1.
Qed.

Lemma acc_all : forall b, Acc bool_lt b.
Proof.
  Hint Constructors bool_is_value sexp_is_value.
  Hint Resolve acc_true acc_false acc_eq acc_mem.
  Ltac foobar y H1 H2 := constructor ; intros ; destruct y ; inversion H1 ; auto ; inversion H2.
  induction b ; try (solve [foobar y H H0]).
  * apply acc_eq.
  * apply acc_mem.
  * constructor.
    intros.
    destruct y ; inversion H; subst; auto ; try (solve [inversion H0]).
  * constructor.
    intros.
    destruct y ; inversion H; subst; auto ; try (solve [inversion H0]).
Qed.

Lemma bool_lt_wf : well_founded bool_lt.
Proof.
  unfold well_founded.
  apply acc_all.
Qed.

Require Import Relation_Operators.

Lemma rel_trans : forall A (R: A -> A -> Prop),
    well_founded R -> well_founded (clos_trans A R).
Proof.
  intros.
  unfold well_founded.
  unfold well_founded in H.
  specialize Acc_inv. intros.
  specialize (H0 A R).
  intros.
  induction (H a).
  * constructor.
    intros.
    induction H3.
    - auto.
    - intuition.
      eapply IHclos_trans1; auto.
      intros.
      specialize (Acc_inv H4).
      crush.
Qed.

Definition bool_lt_trans := clos_trans bool bool_lt.
Definition bool_lt_trans_wf : well_founded bool_lt_trans := rel_trans bool_lt_wf.


Definition bool_step : forall (Sigma: var_store_stack)
                              (pi: principals),
    bool -> (bool_value + error).
  intros Sigma pi.
  refine (
      Fix bool_lt_trans_wf
          (fun _ => (sum bool_value error))
          (fun (b: bool)
               (bool_step : forall y : bool, bool_lt_trans y b -> (bool_value + error)) =>
             match b as b' return b = b' -> (bool_value + error) with
             | True => fun _ => inl (exist _ True TrueIsValue)
             | False => fun _ => inl (exist _ False FalseIsValue)
             | Conj l r =>
               fun _ =>
                 match bool_step l _ as linner, bool_step r _ as rinner
                       return (bool_step l _) = linner ->
                              (bool_step r _) = rinner ->
                              (bool_value + error)
                 with
                 | inl lv, inl rv =>
                   fun _ _ =>
                     match (proj1_sig lv) as lv', (proj1_sig rv) as rv'
                           return (proj1_sig lv)=lv' ->
                                  (proj1_sig rv)=rv' ->
                                  (bool_value + error)
                     with
                     | True, True =>
                       fun _ _ => inl (exist _ True _)
                     | False, _ =>
                       fun _ _ => inl (exist _ False _)
                     | _, False =>
                       fun _ _ => inl (exist _ False _)
                     | _, _ =>
                       fun _ _ => inr (BoolEvalErr b)
                     end eq_refl eq_refl
                 | inr err, _ =>
                   fun _ _ => inr err
                 | _, inr err =>
                   fun _ _ => inr err
                 end eq_refl eq_refl
             | Disj l r =>
               fun _ =>
                 match bool_step l _ as linner, bool_step r _ as rinner
                       return (bool_step l _) = linner ->
                              (bool_step r _) = rinner ->
                              (bool_value + error)
                 with
                 | inl lv, inl rv =>
                   fun _ _ =>
                     match (proj1_sig lv) as lv', (proj1_sig rv) as rv'
                           return (proj1_sig lv)=lv' ->
                                  (proj1_sig rv)=rv' ->
                                  (bool_value + error)
                     with
                     | False, False =>
                       fun _ _ => inl (exist _ False _)
                     | True, _ =>
                       fun _ _ => inl (exist _ True _)
                     | _, True =>
                       fun _ _ => inl (exist _ True _)
                     | _, _ =>
                       fun _ _ => inr (BoolEvalErr b)
                     end eq_refl eq_refl
                 | inr err, _ =>
                   fun _ _ => inr err
                 | _, inr err =>
                   fun _ _ => inr err
                 end eq_refl eq_refl
             | Eq l r =>
               fun _ =>
                 match (sexp_step l Sigma pi) as lv', (sexp_step r Sigma pi) as rv'
                       return (sexp_step l Sigma pi)=lv' ->
                              (sexp_step r Sigma pi)=rv' ->
                              (bool_value + error)
                 with
                 | inl (exist _ linner _),
                   inl (exist _ rinner _) =>
                   fun _ _ =>
                     match linner as linner',
                                     rinner as rinner'
                           return linner=linner' ->
                                  rinner=rinner' ->
                                  (bool_value + error) with
                     | (Cons ll lr), (Cons rl rr) =>
                       fun _ _ =>
                         bool_step (Conj (Eq ll rl) (Eq lr rr)) _
                     | _, _ =>
                       fun _ _ => inl (exist _ False _)
                     end eq_refl eq_refl
                 | inr err, _ =>
                   fun _ _ => inr err
                 | _, inr err =>
                   fun _ _ => inr err
                 end eq_refl eq_refl
             | Mem l r =>
               fun _ =>
                 match (sexp_step l Sigma pi) as lv', (sexp_step r Sigma pi) as rv'
                       return (sexp_step l Sigma pi)=lv' ->
                              (sexp_step r Sigma pi)=rv' ->
                              (bool_value + error)
                 with
                 | inl (exist _ linner _),
                   inl (exist _ rinner _) =>
                   fun _ _ =>
                     match linner as linner', rinner as rinner'
                           return linner = linner' ->
                                  rinner = rinner' ->
                                  (bool_value + error) with
                     | lv, Cons rl rr =>
                       fun _ _ =>
                         bool_step (Disj (Eq lv rl) (Mem lv rr)) _
                     | _, _ =>
                       fun _ _ =>
                         inl (exist _ False _)
                     end eq_refl eq_refl
                 | inr err, _ =>
                   fun _ _ => inr err
                 | _, inr err =>
                   fun _ _ => inr err
                 end eq_refl eq_refl
             end eq_refl)) ; auto.
  Unshelve.
  * subst. intuition.
    assert (sexp_is_value (Cons ll lr)). auto.
    assert (sexp_is_value (Cons rl rr)). auto.
    destruct l ; destruct r ; try discriminate.
  - unfold sexp_step in e0 ; try discriminate.
    assert (~sexp_is_value (Var n v)). unfold not. intros. inversion H1.
      eapply t_trans with (Eq (Cons ll lr) (Cons rl rr)).
      inversion s0. inversion s2.
      + constructor. eapply EqLt ; auto.
      + eapply t_trans with (Eq (Cons ll lr) (Var n0 v0)) ; constructor.
        ** eapply SexpValueLtEqR; auto.
           unfold not. intros. inversion H2.
        ** eapply SexpValueLtEqL; auto.
    - subst.
      eapply t_trans with (Eq (Cons ll lr) (Cons rl rr)) ;
      destruct (is_sexp_value (Cons r1 r2)).
      + constructor.
        inversion H. inversion H0.
        eapply EqLt; auto.
      + constructor.
        inversion H. inversion H0.
        eapply EqLt; auto.
      + specialize canonical_sexp_value with (Cons r1 r2) Sigma pi s3.
        intros.
        rewrite H1 in e1.
        assert ((Cons rl rr) = (Cons r1 r2)). injection e1. intros. crush.
        constructor.
        rewrite H2.
        eapply SexpValueLtEqL; auto.
        unfold not. intros. inversion H3.
      + eapply t_trans with (Eq (Cons ll lr) (Cons r1 r2)).
        ** constructor. eapply SexpValueLtEqR; auto.
        **constructor. eapply SexpValueLtEqL; auto.
          unfold not. intros. inversion H1.
    - unfold sexp_step in e0 ; try discriminate.
      fold sexp_step in e0.
      eapply t_trans with (Eq (Cons ll lr) (Cons rl rr)) ;
      destruct (is_sexp_value (Cons l1 l2)).
      + constructor.
        inversion H. inversion H0.
        eapply EqLt; auto.
      + constructor.
        inversion H. inversion H0.
        eapply EqLt; auto.
      + specialize canonical_sexp_value with (Cons l1 l2) Sigma pi s3.
        inversion s3.
        specialize canonical_sexp_value with l1 Sigma pi H3.
        specialize canonical_sexp_value with l2 Sigma pi H4.
        intros.
        destruct (sexp_step l1 Sigma pi).
        ** destruct s6.
           destruct (sexp_step l2 Sigma pi).
           -- destruct s7.
              subst.
              assert ((Cons ll lr) = (Cons l1 l2)).
              crush.
              rewrite H1.
              constructor.
              eapply SexpValueLtEqR; auto.
              unfold not. intros. inversion H2.
           -- discriminate.
              ** discriminate.
      + eapply t_trans with (Eq (Cons l1 l2) (Cons rl rr)).
        ** constructor. eapply SexpValueLtEqL; auto.
        **constructor. eapply SexpValueLtEqR; auto.
          unfold not. intros. inversion H1.
    - inversion H. inversion H0. subst.
      destruct (is_sexp_value (Cons l1 l2));
        destruct (is_sexp_value (Cons r1 r2)).
      + specialize canonical_sexp_value with (Cons l1 l2) Sigma pi s3.
        specialize canonical_sexp_value with (Cons r1 r2) Sigma pi s4.
        intros.
        rewrite H2 in e0.
        rewrite H1 in e1.
        injection e0.
        injection e1.
        intros.
        constructor.
        rewrite H5.
        rewrite H6.
        rewrite H9.
        rewrite H10.
        eapply EqLt; auto.
      + eapply t_trans with (Eq (Cons ll lr) (Cons rl rr)).
        constructor. eapply EqLt; auto.
        specialize canonical_sexp_value with (Cons l1 l2) Sigma pi s3.
        intros.
        rewrite H1 in e0.
        injection e0.
        intros.
        rewrite H2. rewrite H5.
        constructor.
        eapply SexpValueLtEqR; auto.
      + eapply t_trans with (Eq (Cons ll lr) (Cons rl rr)).
        constructor. eapply EqLt; auto.
        specialize canonical_sexp_value with (Cons r1 r2) Sigma pi s3.
        intros.
        rewrite H1 in e1.
        injection e1.
        intros.
        rewrite H2. rewrite H5.
        constructor.
        eapply SexpValueLtEqL; auto.
      + eapply t_trans with (Eq (Cons ll lr) (Cons rl rr)).
        constructor. eapply EqLt; auto.
        eapply t_trans with (Eq (Cons ll lr) (Cons r1 r2)).
        constructor. eapply SexpValueLtEqR; auto.
        constructor. eapply SexpValueLtEqL; auto.
  * subst.
    destruct (is_sexp_value l);
      destruct (is_sexp_value r).
    - specialize (@canonical_sexp_value_2 r (Cons rl rr) Sigma pi s2 s4 e1).
      specialize (@canonical_sexp_value_2 l lv Sigma pi s0 s3 e0).
      intros.
      rewrite H, H0.
      constructor.
      inversion s2.
      eapply MemLt; auto.
    - eapply t_trans with (Mem lv (Cons rl rr)).
      constructor.
      inversion s2.
      eapply MemLt; auto.
      specialize (@canonical_sexp_value_2 l lv Sigma pi s0 s3 e0).
      intros.
      rewrite H.
      constructor.
      eapply SexpValueLtMemR; auto.
    - specialize (@canonical_sexp_value_2 r (Cons rl rr) Sigma pi s2 s3 e1).
      intros.
      rewrite H.
      eapply t_trans with (Mem lv (Cons rl rr)).
      constructor.
      inversion s2.
      eapply MemLt; auto.
      constructor.
      eapply SexpValueLtMemL; auto.
    - eapply t_trans with (Mem lv (Cons rl rr)).
      constructor.
      inversion s2.
      eapply MemLt; auto.
      eapply t_trans with (Mem l (Cons rl rr)).
      constructor.
      eapply SexpValueLtMemL; auto.
      constructor.
      eapply SexpValueLtMemR; auto.

      * constructor.
        subst.
        solve [ eapply ConjLtR
              | eapply DisjLtR
              | eapply ConjLtL
              | eapply DisjLtL
              ].

      * constructor.
        subst.
        solve [ eapply ConjLtR
              | eapply DisjLtR
              | eapply ConjLtL
              | eapply DisjLtL
              ].

      * constructor.
        subst.
        solve [ eapply ConjLtR
              | eapply DisjLtR
              | eapply ConjLtL
              | eapply DisjLtL
              ].

      * constructor.
        subst.
        solve [ eapply ConjLtR
              | eapply DisjLtR
              | eapply ConjLtL
              | eapply DisjLtL
              ].
Qed.

Definition merge_variable (Sig_o Sig_t: var_store_stack) (pi: principals) (mu: mergers) (key: node*var) (hval: sexp_value) (optsig: var_store + error)
  : (var_store + error) :=
  let (n, v) := key in
  let orig_var := lookup n v Sig_o in
  let curr_var := lookup n v Sig_t in
  let sho := mu n v in
  match optsig, orig_var, curr_var, sho with
  | inl acc, inl oval, inl cval, Some sh =>
    let hsig := set_env empty_env "scratch" "hypo" hval in
    let osig := set_env hsig "scratch" "orig" oval in
    let csig := set_env osig "scratch" "curr" cval in
    match sexp_step sh (cons csig Sig_t) pi with
    | inl val =>
      inl (set_env acc n v val)
    | inr err => inr err
    end
  | _, _, _, None => inr (MergeErr n v mu)
  | inl acc, _, _, _ => inl acc
  | inr err, _, _, _ => inr err
  end.

Fixpoint com_step (c: com) (sigma: var_store) (Sigma: var_store_stack) (omega: world_store) (pi: principals) (rho: location) (eta: handlers) (mu: mergers) : (var_store * world_store) + error :=
  match c with
  | Skip => inl (sigma, omega)
  | Seq l r =>
    match com_step l sigma Sigma omega pi rho eta mu with
    | inl (sigma', omega') =>
      com_step r sigma' Sigma omega' pi rho eta mu
    | inr err => inr err
    end
  | If b t f =>
    match bool_step (cons sigma Sigma) pi b as b' with
    | inl (exist _ True _) => com_step t sigma Sigma omega pi rho eta mu
    | inl (exist _ False _) => com_step f sigma Sigma omega pi rho eta mu
    | inl _ => inr (BoolEvalErr b)
    | inr err => inr err
    end
  | With n c' =>
    com_step c' sigma Sigma omega (cons n pi) rho eta mu
  | At n c' =>
    com_step c' sigma Sigma omega pi n eta mu
  | Handle n v op sh sm c' =>
    let eta' := set_handler eta op n v sh in
    let mu' := set_merger mu n v sm in
    com_step c' sigma Sigma omega pi rho eta' mu'
  | Op op =>
    match eta op with
    | Some (n, v, s) =>
      match sexp_step s (cons sigma Sigma) pi with
      | inl s' =>
        match set_mem string_dec n pi with
        | true =>
          let sigma' := set_env sigma n v s' in
          inl (sigma', omega)
        | false => inr (WritePermErr n v pi)
        end
      | inr err => inr err
      end
    | None => inr (HandleErr op eta)
    end
  | Hyp w c =>
    match com_step c empty_env (cons sigma Sigma) empty_world_store pi rho eta mu with
    | inl (sigma', omega') =>
      let omega'' := set_world_store omega w (cons sigma Sigma) sigma' in
      inl (sigma, omega')
    | inr err => inr err
    end
  | Commit w =>
    match omega w with
    | Some (Sigma_o, sigma_h) =>
      let merge_fold := (merge_variable Sigma_o (cons sigma Sigma) (cons "scratch" pi) mu) in
      match StringPairMap.fold merge_fold sigma_h (inl sigma) with
      | inl sigma' => inl (sigma', omega)
      | inr err => inr err
      end
    | None => inr (CommitErr w omega)
    end
  end.

Definition run (c: com) :=
  match com_step c empty_env nil empty_world_store nil "" empty_handlers empty_mergers with
  | inl (sigma, omega) => inl sigma
  | inr err => inr err
  end.

Definition test_com := (Seq (With "alice" (Handle "alice" "times" "__tmp" (Cons EmptySet (Cons EmptySet (Cons EmptySet (Cons EmptySet EmptySet)))) EmptySet (Op "__tmp"))) (Seq (With "bob" (Handle "bob" "times" "__tmp" (Cons EmptySet (Cons EmptySet (Cons EmptySet (Cons EmptySet EmptySet)))) EmptySet (Op "__tmp"))) (With "alice" (Seq (Handle "alice" "fitness" "__tmp" EmptySet EmptySet (Op "__tmp")) (Seq (Handle "alice" "fitness" "set_fitness" (Cons (Var "alice" "fitness") (Var "bob" "fitness")) (Cons (Var "scratch" "orig") (Cons (Var "scratch" "hypo") (Var "scratch" "curr"))) (Hyp "world" (At "DataCenter" (With "Bob" (Op "set_fitness"))))) (Commit "world")))))).

Eval native_compute in (run test_com).
