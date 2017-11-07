Require Import CpdtTactics FunctionalExtensionality.

Definition eq_dec (A: Type) := forall (l r: A), {l = r} + {l <> r}.
Hint Unfold eq_dec.
Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

Theorem eq_dec_eq :
  forall (A: Type)
         (leq req: (forall (l r: A), {l = r} + {l <> r})),
    leq = req.
Proof.
  intros A leq req.
  extensionality foo.
  extensionality bar.
  destruct (leq foo bar) ; destruct (req foo bar) ;
    try (specialize (proof_irrelevance (foo = bar) e e0)) ;
    try (specialize (proof_irrelevance (foo <> bar) n n0)) ;
    crush.
Qed.

Module Type SmallMap.
  Parameter t : Type -> Type.
  Parameter key : Type.

  Parameter eq_dec_key : eq_dec key.
  Parameter eq_dec_t : forall (val: Type) (eq_dec_val: eq_dec val), eq_dec (t val).

  Parameter empty : forall (val: Type) (eq_dec_val: eq_dec val), t val.

  Parameter get : forall (val: Type) (edv : eq_dec val),
      (t val) -> key -> val -> Prop.

  Parameter set : forall (val: Type) (edv : eq_dec val),
      (t val) -> key -> val -> (t val) -> Prop.

  Axiom empty_is_empty :
    forall vt edv k v,
    ~ get vt edv (empty vt edv) k v.

  Axiom get_unique :
    forall vt edv k v v' m,
      get vt edv m k v ->
      get vt edv m k v' ->
      v = v'.

  Axiom set_assigns :
    forall vt edv k (v: vt) m m',
    set vt edv m k v m' ->
    get vt edv m' k v.

  Axiom set_maintains :
    forall vt edv k v m m',
      set vt edv m k v m' ->
      forall k' v',
        k <> k' ->
        get vt edv m k' v' ->
        get vt edv m' k' v'.

  Axiom set_conservative :
    forall vt edv k v m m',
    set vt edv m k v m' ->
    forall k' v',
      k <> k' ->
      get vt edv m' k' v' ->
      get vt edv m k' v'.
End SmallMap.

Module PairMap (L R: SmallMap) <: SmallMap.
  Open Scope type.
  Definition key := L.key * R.key.

  Definition eq_dec_key : eq_dec key.
  Proof.
    specialize L.eq_dec_key.
    specialize R.eq_dec_key.
    unfold eq_dec.
    decide equality.
  Qed.

  Section Val.
    Variable val : Type.
    Variable eq_dec_val : eq_dec val.

    Definition t := L.t (R.t val).

    Definition eq_dec_t : eq_dec t.
    Proof.
      specialize (L.eq_dec_t (R.t val)).
      unfold eq_dec.
      intros.
      specialize (X (R.eq_dec_t val eq_dec_val) l r).
      auto.
    Qed.

    Definition empty := L.empty (R.t val) (R.eq_dec_t val eq_dec_val).

    Inductive get' : t -> key -> val -> Prop :=
    | PropGet : forall edv
                       (lt: t) (rt: R.t val)
                       (lk: L.key)
                       (rk: R.key) (v: val),
        L.get (R.t val) (R.eq_dec_t val edv) lt lk rt ->
        R.get val eq_dec_val rt rk v ->
        get' lt (lk,rk) v.

    Definition get := get'.


    Definition get_unique :
      forall k v v' m,
        get m k v ->
        get m k v' ->
        v = v'.
    Proof.
      intros.
      inversion H.
      inversion H0.
      specialize eq_dec_eq with val edv0 edv. intuition. subst.
      specialize eq_dec_eq with val eq_dec_val edv. intuition. subst.
      assert (rt0 = rt).
      specialize (L.get_unique (R.t val) (R.eq_dec_t val edv) lk rt rt0 m H1).
      intuition.
      crush.
      specialize (R.get_unique val eq_dec_val rk v v' rt).
      crush.
    Qed.

    Theorem empty_is_empty :
      forall k v,
        ~ get empty k v.
    Proof.
      destruct k.
      intuition.
      inversion H.
      specialize eq_dec_eq with val edv eq_dec_val. intuition. subst.
      specialize (L.empty_is_empty (R.t val) (R.eq_dec_t val eq_dec_val) k rt).
      crush.
    Qed.

    Inductive set' : t -> key -> val -> t -> Prop :=
    | PropSet : forall
        (lt lt':t) (rt rt': R.t val)
        (lk: L.key) (rk: R.key) (v: val),
        L.get (R.t val) (R.eq_dec_t val eq_dec_val) lt lk rt ->
        R.set val eq_dec_val rt rk v rt' ->
        L.set (R.t val) (R.eq_dec_t val eq_dec_val) lt lk rt' lt' ->
        set' lt (lk,rk) v lt'.

    Definition set := set'.

    Theorem set_assigns :
      forall k v m m',
        set m k v m' ->
        get m' k v.
    Proof.
      intros.
      destruct k.
      inversion H.
      specialize (PropGet eq_dec_val m' rt' k k0 v).
      specialize (L.set_assigns (R.t val) (R.eq_dec_t val eq_dec_val) k rt' m m').
      specialize (R.set_assigns val eq_dec_val k0 v rt rt').
      crush.
    Qed.

    Theorem set_maintains :
    forall k v m m',
      set m k v m' ->
      forall k' v',
        k <> k' ->
        get m k' v' ->
        get m' k' v'.
    Proof.
      intros.
      destruct k, k'.
      inversion H.
      inversion H1.
      specialize eq_dec_eq with val edv eq_dec_val. intuition.
      subst.
      destruct (L.eq_dec_key k k1) ; destruct (R.eq_dec_key k0 k2); subst. crush.
      * specialize (PropGet eq_dec_val m' rt' k1 k2 v').
        intuition.
        assert (rt0 = rt).
        specialize (L.get_unique (R.t val) (R.eq_dec_t val eq_dec_val) k1 rt rt0 m).
        crush.
        subst. intuition.
        assert (L.get (R.t val) (R.eq_dec_t val eq_dec_val) m' k1 rt').
        specialize (L.set_assigns (R.t val) (R.eq_dec_t val eq_dec_val) k1 rt' m m' H9).
        crush.
        assert (R.get val eq_dec_val rt' k2 v').
        specialize (R.set_maintains val eq_dec_val k0 v rt rt' H6 k2 v').
        crush.
        crush.
      * specialize (PropGet eq_dec_val m' rt0 k1 k2 v').
        intuition.
        assert (L.get (R.t val) (R.eq_dec_t val eq_dec_val) m' k1 rt0).
        specialize (L.set_maintains (R.t val) (R.eq_dec_t val eq_dec_val)
                                    k rt' m m' H9 k1 rt0).
        intuition.
        intuition.
      * specialize (PropGet eq_dec_val m' rt0 k1 k2 v').
        intuition.
        assert (L.get (R.t val) (R.eq_dec_t val eq_dec_val) m' k1 rt0).
        specialize (L.set_maintains (R.t val) (R.eq_dec_t val eq_dec_val)
                                    k rt' m m' H9 k1 rt0).
        intuition.
        intuition.
    Qed.


    Theorem set_conservative :
      forall k v m m',
        set m k v m' ->
        forall k' v',
          k <> k' ->
          get m' k' v' ->
          get m k' v'.
    Proof.
      intros.
      destruct k, k'.
      inversion H.
      clear H.
      subst.
      intuition.
      inversion H1.
      clear H.
      specialize eq_dec_eq with val edv eq_dec_val. intuition.
      subst.
      destruct (L.eq_dec_key k k1) ; destruct (R.eq_dec_key k0 k2); subst. crush.
      * specialize (PropGet eq_dec_val m rt k1 k2 v').
        intuition.
        assert (rt0 = rt').
        specialize (L.set_assigns (R.t val) (R.eq_dec_t val eq_dec_val) k1 rt' m m' H9).
        specialize (L.get_unique (R.t val) (R.eq_dec_t val eq_dec_val) k1 rt' rt0 m').
        crush.
        subst.

        assert (R.get val eq_dec_val rt k2 v').
        specialize (R.set_conservative val eq_dec_val k0 v rt rt' H6 k2 v').
        crush.
        intuition.
      * specialize (PropGet eq_dec_val m rt0 k1 k2 v').
        intuition.
        assert (L.get (R.t val) (R.eq_dec_t val eq_dec_val) m k1 rt0).
        specialize (L.set_conservative (R.t val) (R.eq_dec_t val eq_dec_val)
                                       k rt' m m' H9 k1 rt0).
        intuition.
        intuition.
      * specialize (PropGet eq_dec_val m rt0 k1 k2 v').
        intuition.
        assert (L.get (R.t val) (R.eq_dec_t val eq_dec_val) m k1 rt0).
        specialize (L.set_conservative (R.t val) (R.eq_dec_t val eq_dec_val)
                                       k rt' m m' H9 k1 rt0).
        intuition.
        intuition.
    Qed.

  End Val.
End PairMap.

Module Type DecType.
  Parameter t : Type.
  Axiom t_dec : forall (a1 a2: t), {a1 = a2} + {a1 <> a2}.
End DecType.

Module ListMap (K: DecType) <: SmallMap.
  Open Scope list.
  Open Scope type.
  Definition key := K.t.
  Definition eq_dec_key := K.t_dec.

  Section Val.
    Variable val : Type.
    Variable eq_dec_val : eq_dec val.

    Definition t := list (key * val).

    Definition empty (edv: eq_dec val) : t :=
      nil.

    Definition eq_dec_t : eq_dec t.
    Proof.
      unfold eq_dec.
      specialize eq_dec_key.
      specialize eq_dec_val.
      intros.
      decide equality.
      destruct a, p.
      decide equality.
    Qed.

    Inductive get' : eq_dec val -> t -> key -> val -> Prop :=
    | Head : forall edv t k v, get' edv ((k,v)::t) k v
    | Rest : forall edv t k k' v v',
        k <> k' ->
        get' edv t k v ->
        get' edv ((k',v')::t) k v.

    Definition get := get'.

    Hint Unfold get.
    Hint Constructors get'.

    Theorem empty_is_empty :
      forall edv k v,
        ~ get edv (empty edv) k v.
    Proof.
      crush.
      inversion H.
    Qed.

  Theorem get_unique :
    forall edv k v v' m,
      get edv m k v ->
      get edv m k v' ->
      v = v'.
  Proof.
    intros.
    induction m; inversion H ; inversion H0; crush.
  Qed.

  Lemma get_in :
    forall edv l k v,
      get edv l k v -> List.In (k,v) l.
  Proof.
(*    split.*)
    * induction l.
      - intros. inversion H.
      - intros. inversion H; crush.
        (*
  * induction l.
      - intros. inversion H.
      - intros.
        crush.
        destruct (eq_dec_key k k0) ; destruct (eq_dec_val v v0).
        + crush.
        + crush.
        +
          crush.
          eapply Head.
        inversion H.
        + crush.
        +
    induction l.

    split ;
      induction l; intros ; inversion H; crush.

    destruct (eq_dec_key a0 k).
    * subst.
    eapply Rest.
    * crush.
    right.
    inversion H.
    crush.

    right
    crush.
*)
  Qed.

  Fixpoint remove (k: key) (l: list (key*val)) : list (key*val) :=
    match l with
    | nil => nil
    | (k',v)::t =>
      if K.t_dec k k' then
        remove k t
      else
        (k', v) :: (remove k t)
    end.

  Lemma remove_not_in :
    forall edv l k v, ~get edv (remove k l) k v.
  Proof.
    induction l.
    crush. inversion H.
    intros.
    crush.
    inversion H.
    * crush.
      destruct a.
      destruct (K.t_dec k k0).
    - specialize (IHl k v H). auto.
    - crush.
      * crush.
        destruct a.
        destruct (K.t_dec k k0).
    - specialize (IHl k v H). auto.
    - specialize IHl with k v.
      eapply IHl.
      unfold get.
      crush.
  Qed.


  Inductive set' : eq_dec val -> t -> key -> val -> t -> Prop :=
  | First : forall edv k v map,
      (forall v, ~ List.In (k, v) map) ->
      set' edv map k v ((k,v)::map)
  | Replace :
      forall edv k v v' map,
        List.In (k, v') map ->
        set' edv map k v ((k,v)::(remove k map)).

  Definition set := set'.

  Hint Unfold set.
  Hint Constructors set'.

  Theorem set_assigns :
    forall edv k v m m',
    set edv m k v m' ->
    get edv m' k v.
  Proof.
    intros edv k v m.
    generalize k, v.
    clear k.
    clear v.
    induction m; intros ; inversion H ; crush.
  Qed.

  Lemma remove_maintains :
    forall (l : list (key * val)) (k k' : key) (v: val),
      k <> k' ->
      List.In (k',v) l <-> List.In (k',v) (remove k l).
  Proof.
    split.
    * induction l; intros ; inversion H0.
    - subst.
      unfold List.remove.
      destruct (K.t_dec k k') eqn:?; crush.
    - intuition.
      destruct (K.t_dec k k') eqn:?.
      + subst.
        contradiction remove_not_in with eq_dec_val l k' v.
        crush.
      + unfold remove in *.
        destruct a.
        destruct (K.t_dec k k0) eqn:?.
        ** crush.
        ** right.
           auto.
   * induction l ; intros.
    - crush.
    - crush.
      destruct a.
      edestruct (K.t_dec k k0) ; crush.
  Qed.

  Theorem get_remove :
    forall edv k k' v m,
      k <> k' ->
      get edv m k v <->
      get edv (remove k' m) k v.
  Proof.
    split.
    induction m ; intros ; inversion H0 ; intuition ; subst.
    * crush.
      destruct (K.t_dec k' k); crush.
    * crush.
      destruct (K.t_dec k' k'0); crush.
    * induction m.
      - crush.
      - intros.
        destruct a.
        destruct (K.t_dec k k0) eqn:?.
        + destruct (edv v v0) eqn:?.
          ** crush.
          ** crush.
             destruct (K.t_dec k' k0) eqn:?.
             -- crush.
             -- crush.
                inversion H0.
                ++ crush.
                ++ crush.
        + crush.
          destruct (K.t_dec k' k0).
          ** crush.
          ** inversion H0.
          -- crush.
          -- crush.
  Qed.

  Theorem set_maintains :
    forall k v m m',
    set eq_dec_val m k v m' ->
    forall k' v',
      k <> k' ->
      get eq_dec_val m k' v' ->
      get eq_dec_val m' k' v'.
  Proof.
    intros.
    inversion H.
    crush.
    subst.
    specialize @remove_maintains with m k k' v'.
    intros.
    intuition.
    assert (List.In (k', v') m).
    specialize get_in with eq_dec_val m k' v'. crush.
    intuition.
    apply Rest. auto.
    specialize (get_remove eq_dec_val k' k v' m).
    intuition.
  Qed.

  Theorem set_conservative :
    forall k v m m',
    set eq_dec_val m k v m' ->
    forall k' v',
      k <> k' ->
      get eq_dec_val m' k' v' ->
      get eq_dec_val m k' v'.
  Proof.
    intros.
    inversion H; crush.
    * inversion H1; crush.
    * inversion H1; crush.
      intuition.
      assert (List.In (k', v') (remove k m)).
      inversion H10.
      - crush.
      - specialize get_in with eq_dec_val t0 k' v'. intuition.
      -  specialize @remove_maintains with m k k' v'.
         intuition.
         specialize (get_remove eq_dec_val k' k v' m).
         intuition.
  Qed.
  End Val.
End ListMap.
