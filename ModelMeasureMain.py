import sys
sys.path.append("/usr/local/lib/python3.5/site-packages")

import os
import operator
import pprint
import spot
import buddy
from Hypervisor import *


def product3(left, right):
	# the twa_graph.is_existential() method returns a Boolean, not a spot.trival
	if not (left.is_existential() and right.is_existential()):
		raise RuntimeError("alternating automata are not supported")
	bdict = left.get_dict()
	if right.get_dict() != bdict:
		raise RuntimeError("automata should share their dictionary")
		
	result = wtAutomaton(bdict)
	result.copy_ap_of(left)
	result.copy_ap_of(right)
	
	pairs = []   # our array of state pairs
	sdict = {}
	todo = []
	def dst(ls, rs):
		pair = (ls, rs)
		p = sdict.get(pair)
		if p is None:
			p = result.new_state()
			sdict[pair] = p
			todo.append((ls, rs, p))
			pairs.append((ls, rs)) # name each state
		return p
	
	result.set_init_state(dst(left.get_init_state_number(), 
							  right.get_init_state_number()))

	shift = left.num_sets()
	result.set_acceptance(shift + right.num_sets(),
						  left.get_acceptance() & (right.get_acceptance() << shift))
	
	while todo:
		lsrc, rsrc, osrc = todo.pop()
		for lt in left.out(lsrc):
			for rt in right.out(rsrc):
				cond = lt.cond & rt.cond
				if cond != buddy.bddfalse:
					acc = lt.acc | (rt.acc << shift)
					result.new_wt_edge(osrc, dst(lt.dst, rt.dst), cond, acc, weight=left.getEdgeWeight(left.edge_number(lt)))

	# Remember the origin of our states
	result.set_product_states(pairs)
	
	# Loop over all the properties we want to preserve if they hold in both automata
	for p in ('prop_universal', 'prop_complete', 'prop_weak', 'prop_inherently_weak', 
			  'prop_terminal', 'prop_stutter_invariant', 'prop_state_acc'):
		if getattr(left, p)() and getattr(right, p)():
			getattr(result, p)(True)
	return result

def make_TS(bdict):
	# The bdd_dict is used to maintain the correspondence between the
	# atomic propositions and the BDD variables that label the edges of
	# the automaton.
	if(bdict is None):
		bdict = spot.make_bdd_dict();

	ts = wtAutomaton(bdict)

	write = buddy.bdd_ithvar(ts.register_ap("w"))
	read = buddy.bdd_ithvar(ts.register_ap("r"))
	term = buddy.bdd_ithvar(ts.register_ap("t"))

	# States are numbered from 0.
	ts.new_states(5)
	ts.prop_state_acc(True)
	# The default initial state is 0, but it is always better to
	# specify it explicitely.
	ts.set_init_state(0)

	ts.new_wt_edge(0, 1, write & -read  & -term, weight=0)
	
	ts.new_wt_edge(1, 2, read  & -write & -term, weight=0)
	ts.new_wt_edge(2, 3, read  & -write & -term, weight=0)
	ts.new_wt_edge(3, 4, read  & -write & -term, weight=0)
	ts.new_wt_edge(4, 0, term & -write & -read, weight=0)
	ts.new_wt_edge(3, 0, term & -write & -read, weight=0)
	
	return ts

def run_aut(aut, aut_name):
	with open("figures/"+aut_name+".dot", 'w') as fp:
		if isinstance(aut, wtAutomaton):
			file_str = aut.dot_str()
		else:
			file_str = aut.to_str('dot')
		fp.write(file_str)
		# print(file_str)
	fp.close()

	os.system("dot -Tpdf -O {}.dot".format("figures/"+aut_name))



if __name__ == '__main__':

	spot.setup()

	LTLProp = spot.formula('GFt')
	BA = spot.formula.Not(LTLProp).translate('sbacc', 'BA')

	bdict = BA.get_dict();
	model = make_TS(bdict)

	modelCheck = model.intersecting_run(BA)

	# print(modelCheck)

	tau_ql = wtAutomaton(bdict)
	write = buddy.bdd_ithvar(tau_ql.register_ap("w"))
	read = buddy.bdd_ithvar(tau_ql.register_ap("r"))
	term = buddy.bdd_ithvar(tau_ql.register_ap("t"))

	tau_ql.new_states(model.num_states()+10)
	
	for s in range(0, model.num_states()):
		for t in model.out(s):
			tau_ql.new_wt_edge(t.src, t.dst, t.cond, t.acc, weight=0)

	
	tau_ql.new_wt_edge(1, 7, read  & -write & -term, weight=1)
	tau_ql.new_wt_edge(2, 9, read  & -write & -term, weight=1)
	tau_ql.new_wt_edge(3, 12, read  & -write & -term, weight=1)

	tau_ql.new_wt_edge(7, 9, read  & -write & -term, weight=0)
	tau_ql.new_wt_edge(7, 8, read  & -write & -term, weight=1)

	tau_ql.new_wt_edge(8, 11, read  & -write & -term, weight=0)
	tau_ql.new_wt_edge(8, 10, read  & -write & -term, weight=1)	

	tau_ql.new_wt_edge(9, 12, read  & -write & -term, weight=0)
	tau_ql.new_wt_edge(9, 11, read  & -write & -term, weight=1)	

	tau_ql.new_wt_edge(10, 0, -term & -write & -read, weight=0)
	tau_ql.new_wt_edge(11, 0, -term & -write & -read, weight=0)
	tau_ql.new_wt_edge(12, 0, term & -write & -read, weight=0)
	
	
	hypervisor = Hypervisor(model)
	write = buddy.bdd_ithvar(hypervisor.register_ap("w"))
	read = buddy.bdd_ithvar(hypervisor.register_ap("r"))
	term = buddy.bdd_ithvar(hypervisor.register_ap("t"))
	
	hypervisor.new_states(2)
	hypervisor.prop_state_acc(True)

	hypervisor.new_wt_edge(0, 0, buddy.bddtrue, weight=0)
	hypervisor.new_wt_edge(0, 1, write & -read  & -term, weight=0)
	hypervisor.new_wt_edge(1, 1, buddy.bddtrue, weight=0)
	hypervisor.new_wt_edge(1, 0, -write & -read, weight=0)
	
	
	
	
	hypervisor.addTranCostRelation(0, None)
	hypervisor.addTranCostRelation(1, tau_ql)


	sDistMeasure = hypervisor.semi_product()

	prod = product3(sDistMeasure, BA)
	# prod = spot.product(sDistMeasure, BA)
	
	run_aut(model, "model")
	run_aut(tau_ql, "tau_ql")
	run_aut(BA, "BA")

	run_aut(hypervisor, "hypervisor")
	run_aut(sDistMeasure, "sDistMeasure")
	run_aut(prod, "prod")


	# print(sDistMeasure.optimal_value("FUN_LIM_AVG"))
	print(prod.optimal_value("FUN_LIM_AVG"))

	# opt_vals = prod.optimal_value("FUN_LIM_AVG")
	# print(opt_vals)