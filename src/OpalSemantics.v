Require Import String ListSet CpdtTactics ListSet Wf FMapList
        Coq.Structures.OrderedTypeEx String.

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

Definition sexp_value := {sexp | sexp_is_value sexp}.

Inductive bool :=
| Eq    : sexp -> sexp -> bool
| Mem   : sexp -> sexp -> bool
| Conj  : bool -> bool -> bool
| Disj  : bool -> bool -> bool
| True  : bool
| False : bool.

Definition bool_value := { b: bool | b = True \/ b = False}.

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

Fixpoint string_lt (l r: string) : Prop :=
  match l, r with
  | EmptyString, EmptyString => Logic.False
  | EmptyString, _ => Logic.True
  | String lh lr, String rh rr =>
    match Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii lh) (Ascii.nat_of_ascii rh) with
    | inleft (left _) => Logic.True
    | inleft (right _) => string_lt lr rr
    | inright _ => Logic.False
    end
  | _, _ => Logic.False
  end.

Module String_as_OT <: UsualOrderedType.
  Definition t := string.

  Definition eq := @eq string.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := string_lt.

  Lemma lt_trans : forall x y z : t, string_lt x y -> string_lt y z -> string_lt x z.
  Proof.
    intros x.
    induction x; intros ; destruct z; crush; destruct y; crush.
    specialize IHx with y z.
    do 3 (edestruct Compare_dec.lt_eq_lt_dec; crush).
    destruct s, s0; crush.
    destruct s, s0; crush.
  Qed.

  Lemma lt_not_eq : forall x y : t, string_lt x y -> ~ eq x y.
  Proof.
    intros x.
    induction x ; destruct y ; crush.
    edestruct Compare_dec.lt_eq_lt_dec; crush.
    unfold eq in H0.
    destruct s. crush.
    specialize IHx with y.
    crush.
  Qed.

  Definition compare x y : OrderedType.Compare string_lt eq x y.
  Proof.
    generalize y.
    clear y.
    induction x; intros.
    * destruct y.
      - assert (eq "" "").
        crush.
        constructor 2. auto.
      - constructor 1. crush.
    * destruct y.
      - constructor 3. crush.
      - remember (Ascii.nat_of_ascii a) as an.
        remember (Ascii.nat_of_ascii a0) as a0n.
        specialize Ascii.ascii_nat_embedding with a.
        specialize Ascii.ascii_nat_embedding with a0.
        intros.
        specialize IHx with y.
        destruct Compare_dec.lt_eq_lt_dec with an a0n ;
          try (destruct s) ;
          inversion IHx;
          [> constructor 1 ..
          | constructor 2
          | constructor 3
          | constructor 3
          | constructor 3
          | constructor 3 ] ;
          crush ;
          edestruct Compare_dec.lt_eq_lt_dec;
          crush.
  Qed.

  Definition eq_dec := string_dec.
End String_as_OT.

Module NodeVar_OT := PairOrderedType String_as_OT String_as_OT.
Module NodeVarMap := FMapList.Make(NodeVar_OT).

Definition append2 := append.
Definition append3 (s1 s2 s3: string) : string :=
  (append (append s1 s2) s3).
Definition append4 (s1 s2 s3 s4: string) : string :=
  (append (append s1 s2) (append s3 s4)).

Definition var_store := NodeVarMap.t sexp_value.
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

Definition empty_env : var_store := NodeVarMap.empty sexp_value.

Definition set_env (e: var_store) (n: node) (v: var) (val: sexp_value) : var_store :=
  NodeVarMap.add (n, v) val e.

Definition get_env (e: var_store) (n: node) (v: var) : option sexp_value :=
  NodeVarMap.find (n, v) e.

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

Program Fixpoint sexp_step (s: sexp) (Sigma: var_store_stack) (pi: principals)
  : (sexp_value + error) :=
  match s with
  | EmptySet => inl EmptySet
  | Cons l r =>
    match (sexp_step l Sigma pi), (sexp_step r Sigma pi) with
    | inl lv, inl rv =>
      inl (Cons lv rv)
    | inr err, _ => inr err
    | _, inr err => inr err
    end
  | Var n v =>
    match set_mem string_dec n pi with
    | true => lookup n v Sigma
    | false => inr (ReadPermErr n v pi)
    end
  end.
Next Obligation.
eapply ConsValuesIsValue; destruct (_: sexp_value); auto.
Defined.

Inductive bool_lt : bool -> bool -> Prop :=
| FakeRelation : forall b1 b2, bool_lt b1 b2
.
Lemma bool_lt_wf : well_founded bool_lt. Admitted.

Definition bool_step : forall (Sigma: var_store_stack)
                              (pi: principals),
    bool -> (bool_value + error).
  intros Sigma pi.
  refine (
      Fix bool_lt_wf
          (fun _ => (sum bool_value error))
          (fun (b: bool)
               (bool_step : forall y : bool, bool_lt y b -> (bool_value + error)) =>
             match b with
             | True => inl (exist _ True _)
             | False => inl (exist _ False _)
             | Conj l r =>
               match (bool_step l _), (bool_step r _) with
               | inl (exist _ True _), inl (exist _ True _) =>
                 inl (exist _ True _)
               | inl _, inl _ => inl (exist _ False _)
               | inr err, _ => inr err
               | _, inr err => inr err
               end
             | Disj l r =>
               match (bool_step l _), (bool_step r _) with
               | inl (exist _ False _), inl (exist _ False _) =>
                 inl (exist _ False _)
               | inl _, inl _ => inl (exist _ True _)
               | inr err, _ => inr err
               | _, inr err => inr err
               end
             | Eq l r =>
               match (sexp_step l Sigma pi),
                     (sexp_step r Sigma pi) with
               | inl (exist _ (Cons ll lr) _),
                 inl (exist _ (Cons rl rr) _) =>
                 let lb := Eq ll rl in
                 let rb := Eq lr rr in
                 bool_step (Conj lb rb) _
               | inl _, inl _ => inl (exist _ False _)
               | inr err, _ => inr err
               | _, inr err => inr err
               end
             | Mem l r =>
               match (sexp_step l Sigma pi),
                     (sexp_step r Sigma pi) with
               | inl (exist _ lv _),
                 inl (exist _ (Cons rl rr) _) =>
                 let lb := Eq lv rl in
                 let rb := Mem lv rr in
                 bool_step (Disj lb rb) _
               | inl _, inl _ => inl (exist _ False _)
               | inr err, _ => inr err
               | _, inr err => inr err
               end
             end)) ; auto ; constructor.
Defined.

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
      match NodeVarMap.fold merge_fold sigma_h (inl sigma) with
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

Eval compute in (run test_com).