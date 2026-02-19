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

syntax "_" : name
syntax "O" : name
syntax "ext" : name
syntax "FW" : name
syntax "id" : name
syntax "loc" : name
syntax "narrower" : name
syntax "wider" : name

/- table events. -/
syntax "W" : annotable_events -- write events
syntax "R" : annotable_events -- read events
syntax "B" : annotable_events -- branch events
syntax "F" : annotable_events -- fence events
syntax "RMW" : annotable_events -- read-modify-write events

syntax "___" : predefined_events -- all events
syntax "IW" : predefined_events -- initial writes
syntax "M" : predefined_events -- memory events, M = W ∪ R
syntax annotable_events : predefined_events

/- defined_relations: -/
syntax "O" : predefined_relations -- empty relation
syntax "rf" : predefined_relations -- read from
syntax "rfe" : predefined_relations -- read from external
syntax "fr" : predefined_relations -- from read
syntax "co" : predefined_relations -- from read
syntax "id" : predefined_relations -- identity
syntax "loc" : predefined_relations -- same location
syntax "ext" : predefined_relations -- external (different pids)
syntax "po" : predefined_relations -- program order
syntax "rmw" : predefined_relations -- read-modify-write

syntax keyword : dsl_term
syntax num : dsl_term
syntax "(" expr ")" : dsl_term
syntax cat_ident : dsl_term

syntax ident : cat_ident
syntax ident ("-" ident)+ : cat_ident

syntax dsl_term:51 : expr

syntax:51 expr:51 "|" expr:50 : expr
syntax expr "&" expr : expr
syntax expr ";" expr : expr
syntax expr "\\" expr : expr
syntax:60 expr:60 "*" expr:61 : expr
syntax expr "^" expr : expr
syntax expr "+" expr : expr
syntax expr "-" expr : expr
syntax:71 expr "^-1" : expr

syntax assertion expr ("as" cat_ident)? : inst
-- The flag is used to witness the assertion, so it doesn't change the states of the execution, we could just ignore it.
syntax "flag" assertion expr "as" expr : inst
syntax "let" cat_ident "=" expr : inst
syntax "enum" cat_ident "=" sepBy(cat_ident, "||")  : inst

syntax "enum" cat_ident "=" sepBy(cat_ident, "||") : inst
-- event class can be R W F B RMW or a custom name like SRCU
syntax "instructions" annotable_events "[" cat_ident "]" : inst

syntax "(*" ident* "*)" : inst
syntax "include" str : inst
