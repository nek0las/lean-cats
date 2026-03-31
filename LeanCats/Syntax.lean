declare_syntax_cat dsl_term
declare_syntax_cat expr
declare_syntax_cat inst
declare_syntax_cat comment
declare_syntax_cat model
declare_syntax_cat assertion
declare_syntax_cat reserved
declare_syntax_cat keyword
declare_syntax_cat primitive
declare_syntax_cat name
declare_syntax_cat statement
declare_syntax_cat definition
declare_syntax_cat constraint
declare_syntax_cat annotable_events
declare_syntax_cat predefined_events
declare_syntax_cat predefined_relations
declare_syntax_cat cat_ident
declare_syntax_cat procedure_call

syntax reserved:41 : expr
syntax primitive : reserved
syntax keyword : reserved
syntax name : reserved
syntax predefined_events : reserved
syntax predefined_relations : reserved

syntax "and" : keyword
syntax "as" : keyword
syntax "begin" : keyword
syntax "call" : keyword
syntax "do" : keyword
syntax "end" : keyword
syntax "enum" : keyword
syntax "flag" : keyword
syntax "forall" : keyword
syntax "from" : keyword
syntax "fun" : keyword
syntax "in" : keyword
syntax "let" : keyword
syntax "match" : keyword
syntax "procedure" : keyword
syntax "rec" : keyword
syntax "scopes" : keyword
syntax "with" : keyword

syntax "classes" : primitive
syntax "linearizations" : primitive
syntax "tag2events" : primitive
syntax "tag2scopes" : primitive

syntax assertion : keyword
syntax "irreflexive" : assertion
syntax "empty" : assertion
syntax "acyclic" : assertion
syntax "~"assertion : assertion

/- table events. -/
syntax "W" : annotable_events -- write events
syntax "R" : annotable_events -- read events
syntax "B" : annotable_events -- branch events
syntax "F" : annotable_events -- fence events
syntax "RMW" : annotable_events -- read-modify-write events
syntax "SRCU" : annotable_events -- srcu events
syntax "IW" : annotable_events -- initial writes
syntax "M" : annotable_events -- memory events, M = W ∪ R
syntax "_" : annotable_events -- all events

syntax annotable_events : predefined_events

/- defined_relations: -/
syntax "O" : predefined_relations -- empty relation
syntax "rf" : predefined_relations -- read from
syntax "fr" : predefined_relations -- from read
syntax "co" : predefined_relations -- from read
syntax "id" : predefined_relations -- identity
syntax "loc" : predefined_relations -- same location
syntax "po" : predefined_relations -- program order
syntax "rmw" : predefined_relations -- read-modify-write
syntax "mb" : predefined_relations -- read-modify-write
syntax "data" : predefined_relations -- data dependencies, starts with a read
syntax "ctrl" : predefined_relations -- control dependencies, starts with a read
syntax "addr" : predefined_relations -- address dependencies, starts with a read
syntax "rmb" : predefined_relations -- read memory barrier, read -> read
syntax "wmb" : predefined_relations -- write memory barrier, write -> write
syntax "fence" : predefined_relations -- fence barrier
syntax "SYNC" : predefined_relations -- SYNC instruction for mips.

syntax keyword : dsl_term
syntax num : dsl_term
syntax "(" expr ")" : dsl_term
syntax cat_ident : dsl_term

syntax ident : cat_ident
syntax ident ("-" ident)+ : cat_ident

syntax dsl_term:51 : expr

syntax:51 expr:51 "|" expr:50 : expr
syntax "~" expr : expr
syntax expr "&" expr : expr
syntax expr ";" expr : expr
syntax expr "\\" expr : expr
syntax:60 expr:60 "*" expr:61 : expr
syntax:70 expr "*" : expr -- Reflexive Transitive Closure.
syntax:70 expr "+" : expr -- Transitive Closure.
syntax expr "^" expr : expr
syntax expr "+" expr : expr
syntax expr "-" expr : expr
syntax expr "?" : expr
syntax:71 expr "^-1" : expr
-- The procedure will return a value, so we can use it in the expression.
syntax dsl_term "(" expr,* ")" : expr

syntax "[" expr "]" : expr
-- Error handling in OCaml, we can just ignore it.
syntax "try" expr "with" expr : expr

syntax assertion expr ("as" cat_ident)? : inst
-- The flag is used to witness the assertion, so it doesn't change the states of the execution, we could just ignore it.
syntax "flag" assertion expr "as" expr : inst
syntax "let" cat_ident "=" expr : inst
syntax "let" cat_ident "(" cat_ident,* ")" "=" expr : inst
syntax "enum" cat_ident "=" sepBy(cat_ident, "||") : inst
-- event class can be R W F B RMW or a custom name like SRCU
syntax "instructions" "{" annotable_events,+ "}" "[" expr "]" : inst

syntax "(*" ident* "*)" : inst
syntax "include" str : inst
