# Muller C-element: c follows a and b when they agree
.model celement
.inputs a b
.outputs c
.graph
a+ c+
b+ c+
c+ a- b-
a- c-
b- c-
c- a+ b+
.marking { <c-,a+> <c-,b+> }
.initial_state !a !b !c
.end
