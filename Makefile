FRAMA_OPTIONS= -wp-rte -wp-timeout 120 -wp-detect  -wp-model Typed -wp-callee-precond
#-wp-rte -kernel-msg-key pp -wp-debug 1 -slevel 5 -wp-print

qstack_pop : qstack.c
	frama-c $(FRAMA_OPTIONS) qstack.c -wp-fct pop
