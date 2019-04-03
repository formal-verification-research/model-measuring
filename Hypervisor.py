import sys
sys.path.append("/usr/local/lib/python3.5/site-packages")

import os
import html
import pprint
import spot
import buddy

import re

import numpy as np

class wtAutomaton(spot.twa_graph):

	def __init__(self, bdict):
		super(wtAutomaton, self).__init__(bdict)

		self._wtRelation = {}

	def new_wt_edge(self, *args, **kargs):

		edge_num = self.new_edge(*args)
		
		weight = 0
		try:
			weight = kargs["weight"]
		except KeyError:
			print("No weight given. Assigning default=0") 

		self._wtRelation[edge_num] = weight

		return edge_num

	def getEdgeWeight(self, edge_num):
		return self._wtRelation[edge_num]


	def dot_str(self):

		dot_str = self.to_str('dot')

		for e in self.edges():
			search_re = re.compile('({0} -> {1} \[label=\<.*(?=\>]))'.format(e.src, e.dst))

			matchObj = search_re.search(dot_str)
			if matchObj:
				dot_str = search_re.sub(r'\1, {0}'.format(self._wtRelation[self.edge_number(e)]), dot_str)

		return dot_str

	def optimal_value(self, cost_function):

		if cost_function=='FUN_SUM':
			return self.sum_function()
		elif cost_function=='FUN_LIM_AVG':
			return self.limit_avg_function()
		else:
			return None

	def findShortestPathXY(self):
		num_vertex = self.num_states()
		
		dp = np.full(shape=(num_vertex+1, num_vertex), fill_value=np.inf, dtype=float)
		dp[0][0] = 0;

		for i in range(1, num_vertex+1):
			
			for j in range(0, num_vertex):
				
				inLink = []
				for l in self.edges():
					if l.dst == j:
						inLink.append(l)

				for e in inLink:
					if dp[i-1][e.src] != np.inf:
						curr_wt = dp[i-1][e.src] + self._wtRelation[self.edge_number(e)]
						dp[i][j] = min(dp[i][j], curr_wt)

		return dp



	# # karps algorithm
	def minimum_mean_cycle(self):
		
		num_vertex = self.num_states()

		pathXY = self.findShortestPathXY()

		pairs = self.get_product_states()
		if pairs:
			print(pairs)

		print(pathXY)
		
		avg = np.full(shape=(num_vertex), fill_value= -np.inf, dtype=float)

		min_avg = float('inf');

		for i in range(0,num_vertex):
			
			if pathXY[num_vertex][i] != np.inf:

				for j in range(0,num_vertex):
					
					if pathXY[j][i] != np.inf:
						
						avg[i] = max(avg[i], (pathXY[num_vertex][i]-pathXY[j][i])/(num_vertex-j))

		return avg


	def limit_avg_function(self):
		scc_i = spot.scc_info(self)
		scc_num = scc_i.scc_count()

		# print(dir(scc_i))


		optimal_values = {}

		for i in range(scc_num):

			print(i)
			
			states = scc_i.states_of(i)

			# print(len(states))
		
			tmp_bdict = spot.make_bdd_dict()
			wt_aut_scc_i = wtAutomaton(tmp_bdict)

			# States are numbered from 0.
			wt_aut_scc_i.new_states(len(states))
			wt_aut_scc_i.prop_state_acc(True)
			wt_aut_scc_i.set_buchi()
			# The default initial state is 0, but it is always better to
			# specify it explicitely.
			wt_aut_scc_i.set_init_state(0)

			state_lut = {}
			st_id = 0
			for e in scc_i.edges_of(i):
				src = e.src
				dst = e.dst
				wt = self._wtRelation[self.edge_number(e)]

				src

				print(src, wt, dst)
				
		
		return optimal_values




	def sum_function(self):

		scc_i = spot.scc_info(self)
		scc_num = scc_i.scc_count()

		# print(dir(scc_i))


		pathToX = self.findShortestPath(self.get_init_state_number())

		# print(pathToX)

		optimal_values = {}

		pairs = self.get_product_states()

		for i in range(scc_num):
			# print(i, [pairs[p] for p in scc_i.states_of(i)])
			# check if the scc is accepting
			if scc_i.is_accepting_scc(i):
				scc_weight = 0
				for e in scc_i.edges_of(i):
					scc_weight += self._wtRelation[self.edge_number(e)]
					print(i, self.edge_number(e))

				print(i, scc_weight)
				if scc_weight == 0:
					scci_states = scc_i.states_on_acc_cycle_of(i)

					if pairs:
						optimal_values[tuple(pairs[p] for p in scci_states)] = pathToX[scci_states[0]]
					else:	
						optimal_values[scci_states] = pathToX[scci_states[0]]
		
		return optimal_values


	def findShortestPath(self, start, end=None):

		D = {}	          # dictionary of final distances
		P = {}	          # dictionary of predecessors
		Q = {}   		  # est.dist. of non-final vert.
		
		# initialize Q and P
		for vertex in range(0, self.num_states()):
			Q[vertex] = float("inf")
			P[vertex] = None
		
		Q[start] = 0
		
		for v in Q: # iterate and pop the smallest item in Q
			D[v] = Q[v]
			if v == end: break # we have reached the end

			for e in self.out(v): # for all of v's adjacent vertices
				w = e.dst
				vwLength = D[v] + self.getEdgeWeight(self.edge_number(e))
				if w not in Q or vwLength < Q[w]:
					Q[w] = vwLength
					P[w] = v

		return D

class Hypervisor(wtAutomaton):

	def __init__(self, model):

		self.Model = model
		super(Hypervisor, self).__init__(self.Model.get_dict())

		self._tranCostRelation = {}

	def addTranCostRelation(self, state, wt_aut):

		if self.get_init_state_number()==state:
			if wt_aut is None:
				self._tranCostRelation[state] = self.Model

			else:
				raise ValueError('For initial state, edges should be None. Automatically assigned from Model. ')
		else:
			if isinstance(wt_aut, wtAutomaton):
				self._tranCostRelation[state] = wt_aut
			else:
				raise TypeError("wt_aut should be a wtAutomaton.")

	def semi_product(self):

		# the twa_graph.is_existential() method returns a Boolean, not a spot.trival
		if not (self.is_existential() and self.Model.is_existential()):
			raise RuntimeError("alternating automata are not supported")
		bdict = self.get_dict()
		if self.Model.get_dict() != bdict:
			raise RuntimeError("automata should share their dictionary")
			
		result = wtAutomaton(bdict)
		result.copy_ap_of(self)
		result.copy_ap_of(self.Model)
		
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
		
		result.set_init_state(dst(self.get_init_state_number(), 
								  self.Model.get_init_state_number()))

		shift = self.num_sets()
		result.set_acceptance(shift + self.Model.num_sets(),
							  self.get_acceptance() & (self.Model.get_acceptance() << shift))
		
		while todo:
			lsrc, rsrc, osrc = todo.pop()
			model_lsrc = self._tranCostRelation[lsrc]
			for lt in self.out(lsrc):
				for rt in model_lsrc.out(rsrc):

					cond = lt.cond & rt.cond
					if cond != buddy.bddfalse:
						acc = lt.acc | (rt.acc << shift)
						weight = self._wtRelation[self.edge_number(lt)] + model_lsrc.getEdgeWeight(model_lsrc.edge_number(rt))
						result.new_wt_edge(osrc, dst(lt.dst, rt.dst), cond, acc, weight=weight)



		# Remember the origin of our states
		result.set_product_states(pairs)
		
		# Loop over all the properties we want to preserve if they hold in both automata
		for p in ('prop_universal', 'prop_complete', 'prop_weak', 'prop_inherently_weak', 
				  'prop_terminal', 'prop_stutter_invariant', 'prop_state_acc'):
			if getattr(self, p)() and getattr(self.Model, p)():
				getattr(result, p)(True)
		return result



			



if __name__ == '__main__':

	spot.setup()

	# m = spot.translate("Floss", "BA", "sbacc")
	
	# h = Hypervisor(m)
	# test = buddy.bdd_ithvar(h.register_ap("test"))

	# h.new_states(2)
	# h.new_wt_edge(0, 1, test, weight=11)
	# h.new_wt_edge(1, 0, buddy.bddtrue, weight=3)

	# print(h.dot_str())

	def make_TS(bdict=None):
		# The bdd_dict is used to maintain the correspondence between the
		# atomic propositions and the BDD variables that label the edges of
		# the automaton.
		if(bdict is None):
			bdict = spot.make_bdd_dict();

		ts = wtAutomaton(bdict)

		# States are numbered from 0.
		ts.new_states(4)
		ts.prop_state_acc(True)
		ts.set_buchi()
		# The default initial state is 0, but it is always better to
		# specify it explicitely.
		ts.set_init_state(0)

		# ts.new_wt_edge(0, 1, buddy.bddtrue, weight=1)

		# ts.new_wt_edge(1, 2, buddy.bddtrue, weight=0)
		# ts.new_wt_edge(1, 5, buddy.bddtrue, weight=2)

		# ts.new_wt_edge(2, 3, buddy.bddtrue, weight=2)

		# ts.new_wt_edge(3, 4, buddy.bddtrue, [0], weight=1)

		# ts.new_wt_edge(4, 2, buddy.bddtrue, weight=0)
		# ts.new_wt_edge(4, 5, buddy.bddtrue, weight=0)

		# ts.new_wt_edge(5, 6, buddy.bddtrue, weight=0)
		# ts.new_wt_edge(6, 5, buddy.bddtrue, [0], weight=0)

		ts.new_wt_edge(0, 1, buddy.bddtrue, [0], weight=1); 
		ts.new_wt_edge(0, 2, buddy.bddtrue, [0], weight=10); 
		ts.new_wt_edge(1, 2, buddy.bddtrue, [0], weight=3); 
		ts.new_wt_edge(2, 3, buddy.bddtrue, [0], weight=2); 
		ts.new_wt_edge(3, 1, buddy.bddtrue, [0], weight=0); 
		ts.new_wt_edge(3, 0, buddy.bddtrue, [0], weight=8); 

		# ts.new_wt_edge(0, 1, buddy.bddtrue, weight=0); 
		# ts.new_wt_edge(1, 2, buddy.bddtrue, weight=1); 
		# ts.new_wt_edge(2, 3, buddy.bddtrue, weight=1); 
		# ts.new_wt_edge(3, 0, buddy.bddtrue, weight=1); 

		return ts

	model = make_TS()

	print(model.optimal_value("FUN_LIM_AVG"))





## Final tauql

# tau_ql.new_wt_edge(1, 7, read  & -write & -term, weight=1)
# tau_ql.new_wt_edge(2, 9, read  & -write & -term, weight=1)
# tau_ql.new_wt_edge(3, 12, read  & -write & -term, weight=1)

# tau_ql.new_wt_edge(7, 9, read  & -write & -term, weight=0)
# tau_ql.new_wt_edge(7, 8, read  & -write & -term, weight=1)

# tau_ql.new_wt_edge(8, 11, read  & -write & -term, weight=0)
# tau_ql.new_wt_edge(8, 10, read  & -write & -term, weight=1)	

# tau_ql.new_wt_edge(9, 12, read  & -write & -term, weight=0)
# tau_ql.new_wt_edge(9, 11, read  & -write & -term, weight=1)	

# tau_ql.new_wt_edge(10, 10, -term & -write & -read, weight=0)
# tau_ql.new_wt_edge(11, 11, -term & -write & -read, weight=0)
# tau_ql.new_wt_edge(12, 12, term & -write & -read, weight=0)