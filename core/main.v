Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require String.
Require Import Cpdt.CpdtTactics.
Require Import Lt.

Require Import core.utils.


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


Definition TokenDefinition := String.string.
Definition Token := String.string.

Definition TokenMatches (def: TokenDefinition) (token: Token): Prop := def = token.
Definition TokenMatchesBool def token :=
	{TokenMatches def token} + {~(TokenMatches def token)}.
Obligation Tactic := crush.
Program Definition match_token def token: TokenMatchesBool def token :=
	Reduce (String.string_dec def token).


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

Theorem PathMatchesStream_neither_empty:
	forall path stream, PathMatchesStream path stream -> path <> [] /\ stream <> [].
Proof. intros p s m. inversion m; crush. Qed.
Hint Resolve PathMatchesStream_neither_empty: core.

Theorem PathMatchesStream_length_non_zero:
	forall path stream, PathMatchesStream path stream -> 0 < (length path) /\ 0 < (length stream).
Proof. intros p s m. inversion m; crush. Qed.
Hint Resolve PathMatchesStream_length_non_zero: core.


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

