Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require String.
Require Import Cpdt.CpdtTactics.
Require Import PeanoNat Lt.

Require Import core.utils.

Ltac notHyp P :=
	match goal with
	| [ _ : P |- _ ] => fail 1
	| _ =>
		match P with
		| ?P1 /\ ?P2 => first [notHyp P1 | notHyp P2 | fail 2]
		| _ => idtac
		end
	end.

(*Definition ListsCorrespondBool lt lu :=
	{ListsCorrespond lt lu} + {~(ListsCorrespond lt lu)}.
Obligation Tactic := crush.
Fixpoint lists_correspond
	(corresponder: forall t u, {C t u} + {~(C t u)})
	lt lu
: ListsCorrespondBool lt lu :=
	match lt, lu with
	| [], [] => Yes
	| (t :: lt'), (u :: lu') => if corresponder t u
		then Reduce (lists_correspond corresponder lt' lu')
		else No
	| _, _ => No
	end.*)


(*
skipn_O: forall (l), skipn 0 l = l
skipn_all: forall (l), skipn (length l) l = []
skipn_nil: forall (n), skipn n ([]) = []
skipn_length: forall (n) (l), length (skipn n l) = length l - n
skipn_cons: forall (n) (a: A) (l), skipn (S n) (a :: l) = skipn n l
skipn_all2: forall [n] (l), length l <= n -> skipn n l = []
skipn_app: forall (n) (l1 l2), skipn n (l1 ++ l2) = skipn n l1 ++ skipn (n - length l1) l2

firstn_all: forall (l), firstn (length l) l = l
firstn_O: forall (l), firstn 0 l = []
firstn_le_length: forall (n) (l), length (firstn n l) <= n
firstn_nil: forall (n), firstn n [] = []
removelast_firstn_len: forall (l), removelast l = firstn (Init.Nat.pred (length l)) l
firstn_length: forall (n) (l), length (firstn n l) = Init.Nat.min n (length l)
firstn_all2: forall [n] (l), length l <= n -> firstn n l = l
firstn_skipn: forall (n) (l), firstn n l ++ skipn n l = l
firstn_length_le: forall (l) [n], n <= length l -> length (firstn n l) = n
firstn_cons: forall (n) (a: A) (l), firstn (S n) (a :: l) = a :: firstn n l
firstn_skipn_comm: forall (m n) (l), firstn m (skipn n l) = skipn n (firstn (n + m) l)
skipn_firstn_comm: forall (m n) (l), skipn m (firstn n l) = firstn (n - m) (skipn m l)
firstn_removelast: forall [n] (l), n < length l -> firstn n (removelast l) = firstn n l
combine_firstn_r: forall [A B: Type] (l) (l': list B), combine l l' = combine (firstn (length l') l) l'
combine_firstn_l: forall [A B: Type] (l) (l': list B), combine l l' = combine l (firstn (length l) l')
removelast_firstn: forall [n] (l), n < length l -> removelast (firstn (S n) l) = firstn n l
firstn_app_2: forall (n) (l1 l2), firstn (length l1 + n) (l1 ++ l2) = l1 ++ firstn n l2
firstn_app: forall (n) (l1 l2), firstn n (l1 ++ l2) = firstn n l1 ++ firstn (n - length l1) l2

*)

Theorem skipn_n_smaller_not_nil:
	forall T n (l: list T), n < length l -> skipn n l <> [].
Proof.
	intros ? n; induction n; intros l; induction l; intros; solve_crush;
	solve [simpl in *; apply IHn; crush].
Qed.

Theorem skipn_length_smaller_not_nil:
	forall T (bigger smaller: list T),
		length smaller < length bigger
		-> skipn (length smaller) bigger <> [].
Proof.
	intros; apply skipn_n_smaller_not_nil; crush.
Qed.

Theorem length_cons_equal:
	forall A B a (la: list A) b (lb: list B),
		length (a :: la) = length (b :: lb) -> length la = length lb.
Proof.
	intros; induction la; crush.
Qed.

Ltac add_append_length :=
	repeat match goal with
	| H: ?l = ?a ++ ?b |- _ =>
		first [notHyp (length (a ++ b) = length a + length b) | fail 2]
		|| specialize (app_length a b) as ?
	end.

Ltac add_length_cons_equal :=
	repeat match goal with
		| [ H: length (?t :: ?lt) = length (?u :: ?lu) |- _ ] =>
			first [notHyp (length lt = length lu) | fail 2]
			|| specialize (length_cons_equal H) as ?
	end.


Section ListsCorrespond.
	Variable T U: Type.
	Variable C: T -> U -> Prop.

	Inductive ListsCorrespond: list T -> list U -> Prop :=
		| ListsCorrespond_nil: ListsCorrespond (@nil T) (@nil U)
		| ListsCorrespond_cons: forall (t: T) (u: U) lt lu,
			C t u -> ListsCorrespond lt lu -> ListsCorrespond (t :: lt) (u :: lu)
	.
	Hint Constructors ListsCorrespond: core.

	Theorem ListsCorrespond_same_length:
		forall lt lu, ListsCorrespond lt lu -> length lt = length lu.
	Proof.
		intros ? ? H; induction H; crush.
	Qed.

	Ltac remember_ListsCorrespond :=
		repeat match goal with
		| H: ListsCorrespond ?lt ?lu |- _ =>
			match goal with | _: lt = ?a, _: lu = ?b |- _ => fail 2 end
			|| remember lt; remember lu
		end.

	Ltac add_ListsCorrespond_same_length :=
		repeat match goal with
		| H: ListsCorrespond ?lt ?lu |- _ =>
			first [notHyp (length lt = length lu) | fail 2]
			|| specialize (ListsCorrespond_same_length H) as ?
		end.

	Theorem ListsCorrespond_append:
		forall lt_one lu_one lt_two lu_two,
			ListsCorrespond lt_one lu_one
			-> ListsCorrespond lt_two lu_two
			-> ListsCorrespond (lt_one ++ lt_two) (lu_one ++ lu_two).
	Proof.
		Hint Rewrite -> app_nil_r.
		intros ? ? ? ? H_one H_two; induction H_one; induction H_two; crush.
	Qed.

	Theorem ListsCorrespond_nth_C:
		forall n lt lu,
			ListsCorrespond lt lu
			-> n < length lt \/ n < length lu
			-> exists (Hlt: n < length lt) (Hlu: n < length lu),
				C (safe_nth lt Hlt) (safe_nth lu Hlu).
	Proof.
		intros ? ? ? HC [Hlt | Hlu];
		add_ListsCorrespond_same_length;
		match goal with
		| HC: ListsCorrespond ?lt ?lu, HL: length ?lt = length ?lu |- _ =>
			match goal with
			| _: ?n < length lt |- _ =>
				assert (Hlu: n < length lu) by solve [rewrite <- HL; assumption]
			| _: ?n < length lu |- _ =>
				assert (Hlt: n < length lt) by solve [rewrite -> HL; assumption]
			end
		end;
		exists Hlt; exists Hlu;
		generalize dependent lu; generalize dependent lt;
		induction n; intros; destruct lt; destruct lu; inversion HC; crush.
	Qed.

	Theorem ListsCorrespond_split_lengths:
		forall lt_one lu_one lt_two lu_two,
			ListsCorrespond (lt_one ++ lt_two) (lu_one ++ lu_two)
			-> length lt_one = length lu_one <-> length lt_two = length lu_two.
	Proof.
		intros; remember_ListsCorrespond;
		add_ListsCorrespond_same_length; add_append_length; crush.
	Qed.

	Ltac trivial_ListCorrespond :=
		add_length_cons_equal;
		try match goal with
			| _: context[?l ++ []] |- _ => do 2 rewrite -> app_nil_r in *
		end;
		match goal with
			| |- ListsCorrespond [] [] =>
				solve [apply ListsCorrespond_nil]
			|
				CTU: C ?t ?u,
				HC: ListsCorrespond ?lt ?lu
				|- ListsCorrespond (?t :: ?lt) (?u :: ?lu)
			=>
				solve [apply (ListsCorrespond_cons CTU HC)]

			| HL: length (?t :: ?lt) = length [] |- _ =>
				solve [simpl in HL; discriminate HL]
			| HL: length [] = length (?u :: ?lu) |- _ =>
				solve [simpl in HL; discriminate HL]

			| H: ListsCorrespond [] (?u :: ?lu) |- _ => solve [inversion H]
			| H: ListsCorrespond (?t :: ?lt) [] |- _ => solve [inversion H]

			(*|
				HL: length ?lt_one = length ?lu_one,
				HC: ListsCorrespond (?lt_one ++ ?lt_two) (?lu_one ++ ?lu_two)
			|- _ =>
				let F := fresh "F" in
				assert (F: length lt_two = length lu_two)
					by apply (ListsCorrespond_split_lengths lt_one lu_one lt_two lu_two HC), HL;
				solve [discriminate F]
			|
				HL: length ?lt_two = length ?lu_two,
				HC: ListsCorrespond (?lt_one ++ ?lt_two) (?lu_one ++ ?lu_two)
			|- _ =>
				let F := fresh "F" in
				assert (F: length lt_two = length lu_two)
					by apply (ListsCorrespond_split_lengths lt_one lu_one lt_two lu_two HC), HL;
				solve [discriminate F]*)
		end.

	Theorem ListsCorrespond_append_split:
		forall lt_one lu_one lt_two lu_two,
			ListsCorrespond (lt_one ++ lt_two) (lu_one ++ lu_two)
			-> length lt_one = length lu_one \/ length lt_two = length lu_two
			-> ListsCorrespond lt_one lu_one /\ ListsCorrespond lt_two lu_two.
	Proof.
		intros ?; induction lt_one; intros ? ? ? H [Hlen | Hlen];
		destruct lt_two; destruct lu_one; destruct lu_two; inversion H;
		try match goal with
		|
			HC: ListsCorrespond (?lt_one ++ ?lt_two) (?lu_one ++ ?lu_two),
			HL: length ?lt_two = length ?lu_two
		|- _ =>
			apply (ListsCorrespond_split_lengths lt_one lu_one lt_two lu_two HC) in HL
		end;
		subst; split; try trivial_ListCorrespond;
		try match goal with
		| CTU: C ?t ?u |- ListsCorrespond (?t :: _) (?u :: _) =>
			apply ListsCorrespond_cons; try assumption
		end;
		match goal with
		| IH: forall lu_one lt_two lu_two,
				ListsCorrespond (?lt_one ++ lt_two) (lu_one ++ lu_two)
				-> length ?lt_one = length lu_one \/ length lt_two = length lu_two
				-> ListsCorrespond ?lt_one lu_one /\ ListsCorrespond lt_two lu_two,
			HC: ListsCorrespond (?lt_one ++ ?lt_two) (?lu_one ++ ?lu_two)
			|- ListsCorrespond _ _
		=>
			apply (IHlt_one lu_one lt_two lu_two); crush
		end.
	Qed.

	Theorem ListsCorrespond_split:
		forall n lt lu, ListsCorrespond lt lu
			-> ListsCorrespond (firstn n lt) (firstn n lu)
				/\ ListsCorrespond (skipn n lt) (skipn n lu).
	Proof.
		intros ? ? ? H; specialize (ListsCorrespond_same_length H) as Hlen;
		rewrite <- (firstn_skipn n lt) in H; rewrite <- (firstn_skipn n lu) in H;
		apply (ListsCorrespond_append_split _ _ _ _ H); right;
		do 2 rewrite -> skipn_length; rewrite Hlen; reflexivity.
	Qed.

	Inductive ListsMatch: list T -> list U -> Prop :=
		| ListsMatch_nil: forall lu,  ListsMatch (@nil T) lu
		| ListsMatch_cons: forall (t: T) (u: U) lt lu,
			C t u -> ListsMatch lt lu -> ListsMatch (t :: lt) (u :: lu)
	.
	Hint Constructors ListsMatch: core.

	Theorem ListsMatch_le_length:
		forall lt lu, ListsMatch lt lu -> length lt <= length lu.
	Proof.
		intros ? ? H; induction H; crush.
	Qed.

	Theorem ListsCorrespond_ListsMatch:
		forall lt lu, ListsCorrespond lt lu -> ListsMatch lt lu.
	Proof.
		intros ? ? H; induction H; crush.
	Qed.
	Hint Resolve ListsCorrespond_ListsMatch: core.

	Theorem ListsMatch_same_length_ListsCorrespond:
		forall lt lu,
			ListsMatch lt lu
			-> length lt = length lu
			-> ListsCorrespond lt lu.
	Proof.
		intros ? ? H Hlen.
		induction H; destruct lu; crush.
	Qed.

	Theorem ListsMatch_portion_ListsCorrespond:
		forall lt lu,
			ListsMatch lt lu
			-> exists lu_corr lu_ext,
				lu = lu_corr ++ lu_ext /\ ListsCorrespond lt lu_corr.
	Proof.
		intros ? ? HM;
		exists (firstn (length lt) lu); exists (skipn (length lt) lu); split;
		try solve [symmetry; apply (firstn_skipn (length lt) lu)];
		induction HM; crush.
	Qed.

	Definition list_extends bigger smaller :=
		exists extension: list T, extension <> [] /\ bigger = smaller ++ extension.
	Hint Unfold list_extends: core.

	Theorem ListsCorrespond_extends_longer:
		forall bigger smaller, list_extends bigger smaller
			-> length smaller < length bigger.
	Proof.
		intros ? ? [extension []]; subst;
		induction smaller; destruct extension; crush.
	Qed.

	Theorem ListsCorrespond_extends_corresponds_longer:
		forall bigger smaller smaller_correspond bigger_correspond,
			list_extends bigger smaller
			-> ListsCorrespond smaller smaller_correspond
			-> ListsCorrespond bigger bigger_correspond
			-> length smaller_correspond < length bigger_correspond.
	Proof.
		intros ? ? ? ? extends SC BC;
		rewrite <- (ListsCorrespond_same_length SC);
		rewrite <- (ListsCorrespond_same_length BC);
		apply ListsCorrespond_extends_longer; exact extends.
	Qed.

	(*Theorem ListsMatch_shorter:
		forall total smaller extension matched,
			total = smaller ++ extension
			-> ListsMatch total matched
			-> ListsMatch smaller matched.
	Proof.

	Qed.*)

	(*Theorem ListsCorrespond_extends:
		forall bigger smaller bigger_correspond,
			list_extends bigger smaller
			-> ListsCorrespond bigger bigger_correspond
			-> exists smaller_correspond extension,
				bigger_correspond = smaller_correspond ++ extension
				/\ ListsCorrespond smaller smaller_correspond.
	Proof.

	Qed.*)

	Theorem ListsMatch_extends:
		forall bigger smaller matched,
			list_extends bigger smaller
			-> ListsMatch bigger matched
			-> ListsMatch smaller matched.
	Proof.
		intros ? ? ? [extension [Hne Hb]] Hm; subst; generalize dependent matched;
		induction smaller; intros; destruct matched; inversion Hm; crush.
	Qed.


	(*

	Definition ListsCorrespond_contains bigger smaller :=
		(forall lu, ListsCorrespond smaller lu -> ListsCorrespond bigger lu)
		/\ exists lu, ListsCorrespond bigger lu /\ ~(ListsCorrespond smaller lu).
	Hint Unfold ListsCorrespond_contains: core.

	Theorem ListsCorrespond_extends_equivalent_contains:
		forall smaller bigger,
			list_extends smaller bigger <-> ListsCorrespond_contains smaller bigger.
	Proof.
		unfold list_extends in *; unfold ListsCorrespond_contains in *.
split.

-
intros [extension []].
subst.
split.
	Qed.*)

End ListsCorrespond.

(*Theorem ListsCorrespond_transfer:
	forall T CA CB,
		(forall a b, CA a b <-> CB a b) ->
		forall lta ltb, @ListsCorrespond T T CA lta ltb <-> @ListsCorrespond T T CB lta ltb.
Proof.
split; generalize dependent ltb;
induction lta; intros ltb; induction ltb;
intros HCA; try apply ListsCorrespond_nil; try inversion HCA; subst;

apply ListsCorrespond_cons; crush.
apply H; crush.
Qed.


an interesting idea for matching: if a list extends a smaller one, then it is contradictory to say that the smaller one matches but the bigger one doesn't. this could be the crux of what it means for something to "lookahead".

Definition TokenDefinition := String.string.
Definition Token := String.string.

Definition TokenMatches (def: TokenDefinition) (token: Token): Prop := def = token.
Hint Unfold TokenMatches: core.
Definition TokenMatchesBool def token :=
	{TokenMatches def token} + {~(TokenMatches def token)}.
Obligation Tactic := crush.
Program Definition match_token def token: TokenMatchesBool def token :=
	Reduce (String.string_dec def token).

Definition TokenDefinitionsSame (a b: TokenDefinition): Prop := a = b.
Hint Unfold TokenDefinitionsSame: core.
Definition TokenDefinitionsEquivalent (a b: TokenDefinition): Prop :=
	forall token, TokenMatches a token <-> TokenMatches b token.
Hint Unfold TokenDefinitionsEquivalent: core.

Ltac token_unfold :=
	unfold TokenDefinitionsEquivalent in *;
	unfold TokenDefinitionsSame in *;
	unfold TokenMatches in *.

Theorem TokenDefinitionsSameEquivalent:
	forall a b, TokenDefinitionsSame a b <-> TokenDefinitionsEquivalent a b.
Proof. split; token_unfold; crush. Qed.
Hint Rewrite TokenDefinitionsSameEquivalent: core.


Definition TokenPath := list TokenDefinition.
Definition TokenStream := list Token.

Definition TokenPathsSame a b :=
	@ListsCorrespond TokenDefinition TokenDefinition TokenDefinitionsSame a b.
Hint Unfold TokenPathsSame: core.
Definition TokenPathsEquivalent a b :=
	@ListsCorrespond TokenDefinition TokenDefinition TokenDefinitionsEquivalent a b.
Hint Unfold TokenPathsEquivalent: core.

Ltac path_unfold :=
	unfold TokenPathsEquivalent in *;
	unfold TokenPathsSame in *;
	token_unfold.


Theorem TokenPathsSameEquivalent:
	forall a b, TokenPathsSame a b <-> TokenPathsEquivalent a b.
Proof.
	split; apply (@ListsCorrespond_transfer TokenDefinition TokenDefinitionsSame TokenDefinitionsEquivalent TokenDefinitionsSameEquivalent).
Qed.
Hint Rewrite TokenPathsSameEquivalent: core.

Definition PathMatchesStream path stream :=
	@ListsCorrespond TokenDefinition Token TokenMatches path stream /\ path <> [].
Hint Unfold PathMatchesStream: core.

		(*| [ H: TokenMatches _ _ |- _ ] =>*)
			(*token_unfold; crush*)
Ltac invert_PathMatchesStream :=
	crush; repeat match goal with
		| [ H: PathMatchesStream _ _ |- _ ] =>
			inversion H; clear H; crush
		| [ H: @ListsCorrespond _ _ _ _ _ |- _ ] =>
			inversion H; clear H; crush
	end.

Theorem PathMatchesStream_path_not_empty:
	forall stream, ~(PathMatchesStream [] stream).
Proof. invert_PathMatchesStream. Qed.
Hint Resolve PathMatchesStream_path_not_empty: core.

Theorem PathMatchesStream_stream_not_empty:
	forall path, ~(PathMatchesStream path []).
Proof. destruct path; invert_PathMatchesStream. Qed.
Hint Resolve PathMatchesStream_stream_not_empty: core.

Theorem PathMatchesStream_same_length:
	forall path stream, PathMatchesStream path stream -> length path = length stream.
Proof. intros ? ? [->%ListsCorrespond_same_length]; easy. Qed.

Theorem PathMatchesStream_length_non_zero:
	forall path stream, PathMatchesStream path stream -> 0 <> (length path) /\ 0 <> (length stream).
Proof. invert_PathMatchesStream. Qed.
Hint Resolve PathMatchesStream_length_non_zero: core.





Theorem PathMatchesStream_same_if_match_same_aux :
	forall path stream, PathMatchesStream path stream -> path = stream.
Proof. intros ? ? H. induction H; crush. Qed.

Theorem PathMatchesStream_same_if_match_same:
	forall a b stream,
		PathMatchesStream a stream
		-> PathMatchesStream b stream
		-> a = b.
Proof.
	intros ? ? ? ->%PathMatchesStream_same_if_match_same_aux ->%PathMatchesStream_same_if_match_same_aux.
Qed.




Definition PathSameStartAs (smaller bigger: TokenPath): Prop :=
	smaller <> [] -> bigger <> []
	-> forall stream, PathMatchesStream smaller stream -> PathMatchesStream bigger stream.
Hint Unfold PathSameStartAs: core.

Check PathSameStartAs.

Theorem PathSameStartAs_always_when_same:
	forall a b, a = b -> a <> [] -> PathSameStartAs a b.
Proof. crush. Qed.
Hint Resolve PathSameStartAs_always_when_same: core.

Theorem PathSameStartAs_if_not_then_not_same:
	forall smaller bigger, (~PathSameStartAs smaller bigger) -> smaller <> bigger.
Proof. crush. Qed.
Hint Resolve PathSameStartAs_if_not_then_not_same: core.

(*H: forall stream: TokenStream,
			PathMatchesStream
				(a :: smaller) stream ->
			PathMatchesStream [] stream*)

Theorem PathSameStartAs_B_longer_equal_A:
	forall smaller bigger,
		PathSameStartAs smaller bigger -> length smaller <= length bigger.
Proof.
	unfold PathSameStartAs in *. intros.
	induction smaller.
	- induction bigger; crush.
	- induction bigger.
		+ simpl in *.  apply (IHsmaller H).  rewrite (Nat.nle_succ_0 (length t0)).

			apply <- PathMatchesStream_path_not_empty in H.  apply Nat.nle_succ_0 in IHA.
		+
Qed.

Definition PathSubsumedBy (A B: TokenPath): Prop := PathSameStartAs A B /\ ~(PathSameStartAs B A).







Inductive BaseModifier: Set :=
	(*| Many*)
	| Maybe
	(*| MaybeMany*)
.
Definition Modifier := option BaseModifier.

Definition ModifierOptional (modifier: Modifier): Prop := modifier = Some Maybe.
Definition ModifierOptionalBool modifier :=
	{ModifierOptional modifier} + {~(ModifierOptional modifier)}.
Obligation Tactic := crush.
Program Definition Modifier_optional modifier: ModifierOptionalBool modifier :=
	match modifier with
	| Some m => match m with
		(*| Many => No*)
		| Maybe => Yes
		(*| MaybeMany => Yes*)
		end
	| None => No
	end.

Inductive Node: Type :=
	| consume (modifier: Modifier) (defs: NonEmpty TokenDefinition)
.
Definition Node_modifier (node: Node): Modifier :=
	match node with
	| consume modifier _ => modifier
	end.
Hint Unfold Node_modifier: core.

Inductive NodeMatchesStream: Node -> TokenStream -> Prop :=
	| NodeMatchesStream_consume_required: forall modifier defs stream,
		PathMatchesStream (listOf defs) stream
		-> NodeMatchesStream (consume modifier defs) stream
	| NodeMatchesStream_consume_optional: forall modifier defs,
		ModifierOptional modifier
		-> NodeMatchesStream (consume modifier defs) []
.
Hint Constructors NodeMatchesStream: core.

Theorem Node_non_optional_stream_not_empty:
	forall node stream,
		~(ModifierOptional (Node_modifier node))
		-> NodeMatchesStream node stream
		-> stream <> [].
Proof. intros n s r ma. inversion ma; crush; inversion H. Qed.
Hint Resolve Node_non_optional_stream_not_empty: core.

Theorem Node_non_optional_length_non_zero:
	forall node stream,
		~(ModifierOptional (Node_modifier node))
		-> NodeMatchesStream node stream
		-> 0 < (length stream).
Proof. intros n s r ma. inversion ma; inversion H; crush. Qed.
Hint Resolve Node_non_optional_stream_not_empty: core.

Inductive NodeListMatchesStream: list Node -> TokenStream -> Prop :=
	| NodeListMatchesStream_base: forall node stream,
		NodeMatchesStream node stream
		-> NodeListMatchesStream [node] stream
	| NodeListMatchesStream_append: forall node stream nodes streams,
		NodeMatchesStream node stream
		-> NodeListMatchesStream nodes streams
		-> NodeListMatchesStream (node :: nodes) (app stream streams)
.
Hint Constructors NodeListMatchesStream: core.

(*what's maybe more interesting here is that if you add a non-optional node to any list of nodes, the length of the match will only increase and not merely remain the same*)

Theorem Node_add_non_optional_increases_match_length:
	forall node stream nodes streams,
		~(ModifierOptional (Node_modifier node))
		-> NodeListMatchesStream (node :: nodes) (app stream streams)
		-> (length streams) < (length (stream ++ streams)).
Proof.
	intros n s ns ss r ma. inversion ma; crush. inversion H2; crush. inversion H; crush.
Qed.
*)


(*
a correct lookahead is one that, for some nodes/node lists A and B
- the lookahead head matches A
- if a token stream would match A ++ B, then the lookahead will say yes
- if a token stream would not match A ++ B (but only B?) then it will say no. probably that means that it simply *doesn't* match B??


if the lookahead matches B, then it also must *totally* match A, implying that A is subsumed by B
otherwise, it must not match B but only A
this means there are two ways to construct evidence that a lookahead is correct
- it matches A but not B
- it matches A and B, but B subsumes A

LookaheadCorrect L A B := forall stream, LookaheadYes L A B stream <-> NodeListMatches (A ++ B) stream





If the stream is:

- merely A, does the lookahead match? my first impulse is yes, although whether the *surrounding rule* will match is a much more fraught question
-

*)



(*
now it's all about how to define a "maximal" match
that's what defines a correct lookahead, it will tell us whether to take the current option in such a way that the overall match we produce will be maximal
now just what is maximal????
*)


(*

let's say we have a rule like this that we need to generate lookaheads for
what we really want to know is what lookahead do we need to test when we hit A B
a consume is all or nothing
(A B)? (A)

the lookahead has to be (A B), since merely (A) would falsely enter the ? consume if the


*)

