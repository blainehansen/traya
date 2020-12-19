Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require String.
Require Import Cpdt.CpdtTactics.
Require Import PeanoNat Lt.

(*Require Import core.utils.*)

Definition TokenDefinition := String.string.
Definition Token := String.string.

Definition TokenMatches (def: TokenDefinition) (token: Token): Prop := def = token.
Hint Unfold TokenMatches: core.
(*Definition TokenMatchesBool def token :=
	{TokenMatches def token} + {~(TokenMatches def token)}.
Obligation Tactic := crush.
Program Definition match_token def token: TokenMatchesBool def token :=
	Reduce (String.string_dec def token).*)

Ltac simpl_TokenMatches :=
	unfold TokenMatches in *; subst.

Theorem TokenDefinition_match_same_then_same:
	forall a b token, TokenMatches a token -> TokenMatches b token -> a = b.
Proof. crush. Qed.


Definition TokenPath := list TokenDefinition.
Definition TokenStream := list Token.

Inductive PathMatchesStream: TokenPath -> TokenStream -> Prop :=
	| PathMatchesStream_base: forall def token,
		TokenMatches def token
		-> PathMatchesStream [def] [token]
	| PathMatchesStream_append: forall def token path stream,
		TokenMatches def token
		-> PathMatchesStream path stream
		-> PathMatchesStream (def :: path) (token :: stream)
.
Hint Constructors PathMatchesStream: core.

Ltac invert_PathMatchesStream :=
	crush; repeat match goal with
		| [ H : TokenMatches _ _ |- _ ] =>
			simpl_TokenMatches; crush
		| [ H : PathMatchesStream _ _ |- _ ] =>
			solve [inversion H; clear H; crush]
	end.

Theorem PathMatchesStream_path_not_empty:
	forall stream, ~(PathMatchesStream [] stream).
Proof. invert_PathMatchesStream. Qed.
Hint Resolve PathMatchesStream_path_not_empty: core.

Theorem PathMatchesStream_stream_not_empty:
	forall path, ~(PathMatchesStream path []).
Proof. invert_PathMatchesStream. Qed.
Hint Resolve PathMatchesStream_stream_not_empty: core.

Theorem PathMatchesStream_length_non_zero:
	forall path stream, PathMatchesStream path stream -> 0 < (length path) /\ 0 < (length stream).
Proof. invert_PathMatchesStream. Qed.
Hint Resolve PathMatchesStream_length_non_zero: core.

Theorem PathMatchesStream_same_if_match_same:
	forall a b stream,
		PathMatchesStream a stream
		-> PathMatchesStream b stream
		-> a = b.
Proof.

intros a b stream.
generalize dependent b.
generalize dependent a.

(*induction stream as [| tok stream IHstream].*)
destruct stream as [| tok stream'] eqn:SE.

- invert_PathMatchesStream.
-
intros a b.
destruct a as [| atok a'] eqn:AE; destruct b as [| btok b'] eqn:BE.

+ invert_PathMatchesStream.
+ invert_PathMatchesStream.
+ invert_PathMatchesStream.
+
intros Ha Hb.
induction Ha; induction Hb.
++


++
++
++




injection.

apply IHstream.


++


+

apply IHstream.
+


+


intros a; induction a as [| atok a IHa]; intros b; induction b as [| btok b IHb].

- invert_PathMatchesStream.
- invert_PathMatchesStream.
- invert_PathMatchesStream.

-
induction stream as [| tok stream IHstream].

+ invert_PathMatchesStream.


+
intros Ha Hb.

apply IHa.

(*intros a b stream Ha.
generalize dependent b.
induction Ha.
-
intros b Hb.
unfold TokenMatches in *.
induction Hb.
+

-




intros a.

induction a as [| atok a IHa].

- invert_PathMatchesStream.

-
intros b.
induction b as [| btok b IHb].
-- invert_PathMatchesStream.
--
intros stream.
induction stream as [| tok stream IHstream].
+ invert_PathMatchesStream.
+
intros Ha.
induction Ha; intros Hb; induction Hb.
++ apply IHb.
++ invert_PathMatchesStream.
++
inversion Ha; clear Ha; inversion Hb; clear Hb; invert_PathMatchesStream.
++
apply IHa.
++
*)

(*intros a b stream.
generalize dependent b.
generalize dependent a.
induction stream as [| tok stream IHstream].
- invert_PathMatchesStream.
-
intros a.
induction a as [| atok a IHa].
-- invert_PathMatchesStream.
--
intros b.
induction b as [| btok b IHb].
++ invert_PathMatchesStream.
++
intros Ha Hb.

induction Ha; induction Hb; simpl_TokenMatches.
crush.
invert_PathMatchesStream.*)

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

(*H : forall stream : TokenStream,
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

