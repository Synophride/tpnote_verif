OPTIONS= -wp -wp-timeout 120 
#-wp-rte -kernel-msg-key pp -wp-debug 1 -slevel 5
#  

qstack : qstack.c
	time frama-c $(OPTIONS) qstack.c -wp-fct transfer
