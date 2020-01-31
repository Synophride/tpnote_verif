OPTIONS= -wp -wp-timeout 5
#-wp-rte -kernel-msg-key pp -wp-debug 1
qstack : qstack.c
	frama-c $(OPTIONS) qstack.c -wp-fct transfer


