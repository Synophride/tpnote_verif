OPTIONS= -wp -wp-rte
#-kernel-msg-key pp -wp-debug 1
qstack : qstack.c
	frama-c $(OPTIONS) qstack.c -wp-fct pop


