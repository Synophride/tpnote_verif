OPTIONS= -wp -wp-timeout 40
#-wp-rte -kernel-msg-key pp -wp-debug 1
#  

qstack : qstack.c
	time frama-c $(OPTIONS) qstack.c -wp-fct 


