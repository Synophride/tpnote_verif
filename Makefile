OPTIONS= -wp -wp-timeout 10 -wp-detect  -wp-model Typed
#-wp-rte -kernel-msg-key pp -wp-debug 1 -slevel 5 -wp-print

qstack : qstack.c
	frama-c $(OPTIONS) qstack.c -wp-fct push
