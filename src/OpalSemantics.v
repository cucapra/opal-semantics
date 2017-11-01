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

Record state :=
  mkState {
      sigma : var_store ;
      Sigma : var_store_stack ;
      omega : world_store ;
      pi : principals ;
      rho : location ;
      eta : handlers ;
      mu : mergers
    }.

Definition error := string.

Definition M (A:Type) := state -> (state * A) + error.

Definition ret {A: Type} (x:A) : M A :=
  fun s => inl (s, x).

Definition bind {A B:Type} (m:M A) (f: A -> M B) : M B :=
  fun s1 =>
    match m s1 with
    | inl (s2,v) => f v s2
    | inr err => inr err
    end.

Definition map {A B:Type} (m: M A) (f: A -> B) : M B :=
  fun s1 =>
    match m s1 with
    | inl (s2, v) => inl (pair s2 (f v))
    | inr err => inr err
    end.

Notation "x <- c1 ; c2" :=
  (bind c1 (fun x => c2))
    (right associativity, at level 84, c1 at next level).

Definition err {A:Type} (err: error) : M A := fun s => inr err.

Definition empty_env : var_store := NodeVarMap.empty sexp_value.

Definition set_env (e: var_store) (n: node) (v: var) (val: sexp_value) : var_store :=
  NodeVarMap.add (n, v) val e.

Definition get_env (e: var_store) (n: node) (v: var) : option sexp_value :=
  NodeVarMap.find (n, v) e.

Definition lookup (n: node) (v: var) : M sexp_value :=
  let lookup' :=
      fix lookup' (Sigma: var_store_stack) :=
        match Sigma with
        | nil => inr (append4 "Could not find " n "." v)
        | cons e rest =>
          match get_env e n v with
          | Some res => inl res
          | None => lookup' rest
          end
        end
  in
  fun state =>
    match lookup' (Sigma state) with
    | inl res => inl (state, res)
    | inr error => inr error
    end.

Definition empty_world_store : world_store :=
  fun _ => None.

Definition set_world_store {A:Type} (u: world) (S: var_store_stack) (s: var_store) : M unit :=
  fun state =>
    let w := omega state in
    let world_store :=
        fun u' =>
          match string_dec u u' with
          | left _ => Some (S, s)
          | right _ => w u'
          end
    in
    let state' := mkState (sigma state) (Sigma state) world_store (pi state)
                          (rho state) (eta state) (mu state) in
    inl (state', tt).

Definition check_principals (n: node) : M unit :=
  fun state =>
    match set_mem string_dec n (pi state) with
    | true => inl (state, tt)
    | false => inr (append "No permission to read " n)
    end.

Definition push_principal (n: node) : M unit :=
  fun state =>
    inl (mkState (sigma state) (Sigma state) (omega state) (cons n (pi state))
                 (rho state) (eta state) (mu state),
         tt).

Definition pop_principal : M unit :=
  fun state =>
    match (pi state) with
    | nil => inr "No principal to pop"
    | cons _ rest =>
      inl (mkState (sigma state) (Sigma state) (omega state) rest
                   (rho state) (eta state) (mu state),
           tt)
    end.

Definition set_location (n: node) : M node :=
  fun state =>
      inl (mkState (sigma state) (Sigma state) (omega state) (pi state)
                   n (eta state) (mu state),
           (rho state)).

Definition empty_handlers : handlers :=
  fun _ => None.

Definition set_handler (o: op) (n: node) (v: var) (s: sexp) : M unit :=
  fun state =>
    let h := eta state in
    let h' :=
        fun o' =>
          match string_dec o o' with
          | left _ => Some (n, v, s)
          | right _ => h o'
          end
    in
    let state' := mkState (sigma state) (Sigma state) (omega state) (pi state)
                          (rho state) h' (mu state) in
    inl (state', tt).

Definition empty_mergers : mergers :=
  fun _ _ => None.

Definition set_merger (n: node) (v: var) (s: sexp) : M unit :=
  fun state =>
    let m := mu state in
    let m' :=
        fun n' v' =>
          match (string_dec n n', string_dec v v') with
          | (left _, left _) => Some s
          | _ => m n' v'
          end
    in
    let state' := mkState (sigma state) (Sigma state) (omega state) (pi state)
                          (rho state) (eta state) m' in
    inl (state', tt).

Program Fixpoint sexp_step (s: sexp) : M sexp_value :=
  match s with
  | EmptySet => ret (exist _ EmptySet _)
  | Cons l r =>
    lv <- sexp_step l ;
      rv <- sexp_step r ;
      ret (exist _ (Cons (proj1_sig lv) (proj1_sig rv)) _)
  | Var n v =>
    _  <- check_principals n ;
      val <- lookup n v ;
      ret val
  end.
Next Obligation.
eapply ConsValuesIsValue; destruct (_: sexp_value); auto.
Defined.

Inductive bool_lt : bool -> bool -> Prop :=
| FakeRelation : forall b1 b2, bool_lt b1 b2
.
Lemma bool_lt_wf : well_founded bool_lt. Admitted.

Definition bool_step : bool -> M bool_value.
  refine (
      Fix bool_lt_wf
          (fun _ => M bool_value)
          (fun (b: bool)
               (bool_step : forall y : bool, bool_lt y b -> M bool_value) =>
             match b with
             | True => ret (exist _ True _)
             | False => ret (exist _ False _)
             | Conj l r =>
               lv <- bool_step l _ ;
               rv <- bool_step r _ ;
               match (proj1_sig lv), (proj1_sig rv) with
               | True, True => ret (exist _ True _)
               | _, _ => ret (exist _ False _)
               end
             | Disj l r =>
               lv <- bool_step l _ ;
               rv <- bool_step r _ ;
               match (proj1_sig lv), (proj1_sig rv) with
               | False, False => ret (exist _ False _)
               | _, _ => ret (exist _ True _)
               end
             | Eq l r =>
               lv <- sexp_step l ;
               rv <- sexp_step r ;
               match (proj1_sig lv), (proj1_sig rv) with
               | Cons ll lr, Cons rl rr =>
                 let lb := Eq ll rl in
                 let rb := Eq lr rr in
                 bool_step (Conj lb rb) _
               | _, _ => ret (exist _ False _)
               end
             | Mem l r =>
               lv <- sexp_step l ;
               rv <- sexp_step r ;
               match (proj1_sig lv), (proj1_sig rv) with
               | lv, Cons rl rr =>
                 let lb := Eq lv rl in
                 let rb := Mem lv rr in
                 bool_step (Disj lb rb) _
               | _, _ => ret (exist _ False _)
               end
             end)) ; auto ; constructor.
Defined.

Program Fixpoint com_step (c: com) (state: state) :=
  match c with
  | Skip => ret tt
  | Seq l r =>
    _ <- com_step l ; com_step r
  | If b t f =>
    bv <- bool_step b ;
      match bv with
      | True => com_step t
      | False => com_step f
      | _ => err "Boolean did not evaluate to value!"
      end
  | With n c =>
    fun s =>
      (_ <- push_principal n ;
         _ <- com_step c) s
      pop_principal
  | At n c =>
    n' <- set_location n ;
      _ <- com_step c ;
      _ <- set_location n' ;
      ret tt
  | Hyp n c =>

  end.

Definition merge_variable (Sig_o Sig_t: var_store_stack) (pi: principals) (mu: mergers) (key: node*var) (hval: sexp_value) (optsig: option var_store) : option var_store :=
  let (n, v) := key in
  let orig_var := lookup Sig_o n v in
  let curr_var := lookup Sig_t n v in
  let sho := mu n v in
  match optsig, orig_var, curr_var, sho with
  | Some acc, Some oval, Some cval, Some sh =>
    let hsig := set_env empty_env "scratch" "hypo" hval in
    let osig := set_env hsig "scratch" "orig" oval in
    let csig := set_env osig "scratch" "curr" cval in
    match sexp_step sh (cons csig Sig_t) pi with
    | Some val =>
      Some (set_env acc n v val)
    | None => None
    end
  | Some acc, _, _, _ => Some acc
  | _, _, _, _ => None
  end.

Fixpoint com_step (c: com) : M (var_store * world_store) :=
  match c with
  | Skip => Some (sigma, omega)
  | Seq l r =>
    match com_step l sigma Sigma omega pi rho eta mu with
    | Some (sigma', omega') =>
      com_step r sigma' Sigma omega' pi rho eta mu
    | None => None
    end
  | If b t f =>
    match bool_step b (cons sigma Sigma) pi as b' with
    | Some (exist _ True _) => com_step t sigma Sigma omega pi rho eta mu
    | Some (exist _ False _) => com_step f sigma Sigma omega pi rho eta mu
    | _ => None
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
      | Some s' =>
        match set_mem string_dec n pi with
        | true =>
          let sigma' := set_env sigma n v s' in
          Some (sigma', omega)
        | false =>
          None
        end
      | None => None
      end
    | None => None
    end
  | Hyp w c =>
    match com_step c empty_env (cons sigma Sigma) empty_world_store pi rho eta mu with
    | Some (sigma', omega') =>
      let omega'' := set_world_store omega w (cons sigma Sigma) sigma' in
      Some (sigma, omega')
    | None => None
    end
  | Commit w =>
    match omega w with
    | Some (Sigma_o, sigma_h) =>
      let merge_fold := (merge_variable Sigma_o (cons sigma Sigma) (cons "scratch" pi) mu) in
      match NodeVarMap.fold merge_fold sigma_h (Some sigma) with
      | Some sigma' => Some (sigma', omega)
      | None => None
      end
    | None => None
    end
  end.


Definition run (c: com) :=
  match com_step c empty_env nil empty_world_store nil "" empty_handlers empty_mergers with
  | Some (sigma, omega) => Some sigma
  | None => None
  end.

Definition test_com := (With "Alice" (Seq (Handle "alice" "times" "%tmp" (Cons EmptySet (Cons EmptySet (Cons EmptySet (Cons EmptySet EmptySet)))) EmptySet (Op "%tmp")) (With "Bob" (Seq (Handle "bob" "times" "%tmp" (Cons EmptySet (Cons EmptySet (Cons EmptySet (Cons EmptySet EmptySet)))) EmptySet (Op "%tmp")) (With "Alice" (Seq (Handle "alice" "fitness" "%tmp" EmptySet EmptySet (Op "%tmp")) (Handle "alice" "fitness" "set_fitness" (Cons (Var "alice" "fitness") (Var "bob" "fitness")) (Cons (Var "scratch" "orig") (Cons (Var "scratch" "hypo") (Var "scratch" "curr"))) (Hyp "world" (Seq (At "DataCenter" (With "Bob" (Op "set_fitness"))) (Commit "world")))))))))).

Eval compute in (run test_com).