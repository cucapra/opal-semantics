Require Import CpdtTactics.

Module Type SmallMap.
  Parameter t : Type -> Type.
  Parameter key : Type.

  Parameter empty : forall val: Type, t val.

  Parameter get : forall (val: Type),
      (t val) -> key -> val -> Prop.

  Parameter set : forall (val: Type),
      (t val) -> key -> val -> (t val) -> Prop.

  Axiom set_assigns :
    forall (vt: Type) k (v: vt) m m',
    set vt m k v m' ->
    get vt m' k v.

  Axiom set_maintains :
    forall vt k v m m',
      set vt m k v m' ->
      forall k' v',
        k <> k' ->
        get vt m k' v' ->
        get vt m' k' v'.

  Axiom set_conservative :
    forall vt k v m m',
    set vt m k v m' ->
    forall k' v',
      k <> k' ->
      ~ get vt m k' v' ->
      ~ get vt m' k' v'.
End SmallMap.

Module PairMap (L R: SmallMap) <: SmallMap.
  Open Scope type.
  Definition key := L.key * R.key.
  Section Val.
    Variable val : Type.

    Definition t := L.t (R.t val).

    Definition empty := L.empty (R.t val).

    Inductive get' : t -> key -> val -> Prop :=
    | Foo : forall (lt: t) (rt: R.t val)
                   (lk: L.key)
                   (rk: R.key) (v: val),
        L.get (R.t val) lt lk rt ->
        R.get val rt rk v ->
        get' lt (lk,rk) v.

    Definition get := get'.
  End Val.
End PairMap.

Module Type UnDecType.
  Parameter t : Type.
End UnDecType.

Module Type DecType.
  Include UnDecType.
  Axiom t_dec : forall (a1 a2: t), {a1 = a2} + {a1 <> a2}.
End DecType.

Module ListMap (K: DecType) <: SmallMap.
  Open Scope list.
  Open Scope type.
  Definition key := K.t.
  Section Val.
    Variable val : Type.

    Definition t := list (key * val).

    Inductive get' : t -> key -> val -> Prop :=
    | Head : forall t k v, get' ((k,v)::t) k v
    | Rest : forall h t k v, get' t k v -> get' (h::t) k v.

    Definition get := get'.

    Hint Unfold get.
    Hint Constructors get'.

  Lemma get_in :
    forall l k v,
      get l k v <-> List.In (k,v) l.
  Proof.
    split ;
    induction l; intros ; inversion H; subst ;
    crush ;
    right ;
    crush.
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
    forall l k v, ~get (remove k l) k v.
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
        destruct h, a.
        destruct (K.t_dec k k1).
    - specialize (IHl k v H). auto.
    - specialize IHl with k v.
      eapply IHl.
      unfold get.
      crush.
  Qed.


  Inductive set' : t -> key -> val -> t -> Prop :=
  | First : forall k v map,
      (forall v, ~ List.In (k, v) map) ->
      set' map k v ((k,v)::map)
  | Replace :
      forall k v v' map,
        List.In (k, v') map ->
        set' map k v ((k,v)::(remove k map)).

  Definition set := set'.

  Hint Unfold set.
  Hint Constructors set'.

  Theorem set_assigns :
    forall k v m m',
    set m k v m' ->
    get m' k v.
  Proof.
    intros k v m.
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
        contradiction remove_not_in with l k' v.
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

  Theorem set_maintains :
    forall k v m m',
    set m k v m' ->
    forall k' v',
      k <> k' ->
      get m k' v' ->
      get m' k' v'.
  Proof.
    intros.
    inversion H.
    crush.
    subst.
    specialize @remove_maintains with m k k' v'.
    intros.
    intuition.
    assert (List.In (k', v') m).
    specialize get_in with m k' v'. crush.
    intuition.
    apply Rest.
    specialize get_in with (remove k m) k' v'.
    crush.
  Qed.

  Theorem set_conservative :
    forall k v m m',
    set m k v m' ->
    forall k' v',
      k <> k' ->
      ~ get m k' v' ->
      ~ get m' k' v'.
  Proof.
    intros.
    inversion H; crush.
    * inversion H7; crush.
    * inversion H7; crush.
      contradict H1.
      specialize @remove_maintains with m k k' v'.
      intros.
      assert (List.In (k', v') (remove k m)).
      inversion H7; crush.
      specialize get_in with (remove k m) k' v'. crush.
      intuition.
      specialize get_in with m k' v'. crush.
  Qed.
  End Val.
End ListMap.
