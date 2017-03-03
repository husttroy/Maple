package edu.ucla.cs.mine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;
import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multiset;

import edu.ucla.cs.model.PredicateCluster;
import edu.ucla.cs.utils.SAT;

public abstract class PredicatePatternMiner {
	// id -> predicates (filtered + normalized)
	HashMap<String, HashMap<String, ArrayList<String>>> predicates; 
	ArrayList<String> pattern;
	// api -> clusters of predicates
	HashMap<String, ArrayList<PredicateCluster>> clusters;
	
	public PredicatePatternMiner (ArrayList<String> pattern) {
		this.pattern = new ArrayList<String>();
		for (String p : pattern) {
			if (p.contains("{") || p.contains("}")) {
				continue;
			} else {
				this.pattern.add(p);
			}
		}
		this.clusters = new HashMap<String, ArrayList<PredicateCluster>>();
		this.predicates = new HashMap<String, HashMap<String, ArrayList<String>>>();
	}
	
	protected void merge() {
		Set<String> apis = this.clusters.keySet();
		for(String api : apis) {
			ArrayList<PredicateCluster> arr = this.clusters.get(api);
			ArrayList<PredicateCluster> newArr = merge(arr);
			while (!arr.equals(newArr)) {
				// some clusters have been merged
				// update current clusters
				arr = newArr;
				newArr = merge(newArr);
			}
			
			// update the cluster
			this.clusters.put(api, newArr);
		}
	}

	/**
	 * 
	 * Try to merge the first two cluster in the list
	 * 
	 * @param arr
	 * @return
	 */
	private ArrayList<PredicateCluster> merge(ArrayList<PredicateCluster> arr) {
		ArrayList<PredicateCluster> newArr = new ArrayList<PredicateCluster>(arr);
		SAT sat = new SAT();
		for (int i = 0; i < arr.size(); i++) {
			PredicateCluster pc1 = arr.get(i);
			for (int j = i + 1; j < arr.size(); j++) {
				PredicateCluster pc2 = arr.get(j);
				if (sat.checkEquivalence(pc1.shortest, pc2.shortest)) {
					PredicateCluster merge = new PredicateCluster(pc1, pc2);
					newArr.remove(pc1);
					newArr.remove(pc2);
					newArr.add(merge);
					return newArr;
				}
			}
		}

		return newArr;
	}

	protected void setup() {
		HashMap<String, ArrayList<String>> ps = new HashMap<String, ArrayList<String>>();

		// group predicates based on api first
		for (String id : predicates.keySet()) {
			HashMap<String, ArrayList<String>> api_predicates = predicates
					.get(id);

			for (String api : api_predicates.keySet()) {
				ArrayList<String> preds = api_predicates.get(api);
				ArrayList<String> existing_preds;
				if (ps.containsKey(api)) {
					existing_preds = ps.get(api);
				} else {
					existing_preds = new ArrayList<String>();
				}

				existing_preds.addAll(preds);

				ps.put(api, existing_preds);
			}
		}

		// for each api, cluster its predicates
		for (String api : ps.keySet()) {
			ArrayList<PredicateCluster> hs = new ArrayList<PredicateCluster>();
			ArrayList<String> preds = ps.get(api);
			Multiset<String> set = HashMultiset.create();
			set.addAll(preds);
			for (String pred : set.elementSet()) {
				PredicateCluster pc = new PredicateCluster(pred,
						set.count(pred));
				hs.add(pc);
			}
			clusters.put(api, hs);
		}
	}
	
	protected abstract void loadAndFilterPredicate();
	
	/**
	 * 1. find all method call sequences that satisfy the given pattern 2. for
	 * each API call sequence, find the arguments and receiver of each API in
	 * the pattern 3. for each predicate, filter out those clauses that do not
	 * include these arguments and receiver 4. initially cluster identical
	 * predicates 5. for every two clusters, merge them if they are semantically
	 * equivalent using z3 6. keep merging until a fix point
	 */
	public void process() {
		// load predicates and normalize variable names and condition irrelevant clauses
		loadAndFilterPredicate();
		
		// cluster based on textual similarity
		setup();

		// print initial clusters
		System.out
				.println("Before checking predicate equivalence and merging:");
		for (String api : clusters.keySet()) {
			System.out.println("[" + api + "]");
			int count = 0;
			for (PredicateCluster pc : clusters.get(api)) {
				System.out.print("Cluster" + count + ": ");
				for (String p : pc.cluster.elementSet()) {
					System.out.println(p + "---" + pc.cluster.count(p));
				}
				count++;
			}
		}

		// keep merging predicates until reaching a fix point
		merge();

		System.out.println("After checking predicate equivalence and merging:");
		for (String api : clusters.keySet()) {
			System.out.println("[" + api + "]");
			int count = 0;
			for (PredicateCluster pc : clusters.get(api)) {
				System.out.print("Cluster" + count + ": ");
				for (String p : pc.cluster.elementSet()) {
					System.out.println(p + "---" + pc.cluster.count(p));
				}
				count++;
			}
		}
	}
	
	public String condition(Set<String> vars, String predicate) {
		String[] arr = predicate.split("&&|\\|\\||\\!(?!=)");
		String res = predicate;
		for (String c : arr) {
			c = c.trim();
			if (c.isEmpty() || c.equals("(") || c.equals(")")) {
				continue;
			} else {
				c = SAT.stripUnbalancedParentheses(c);

				boolean flag = false;
				for (String var : vars) {
					if (c.contains(var)) {
						flag = true;
					}
				}

				if (!flag) {
					// this clause is irrelevant
					res = res.replace(c, "true");
				}
			}
		}
		
		// a && !b | a ==> a && !true, which is always evaluated to false
		// Such conditioning  is incomplete because !b should be replaced with true instead of b 
		// So we add the following replacement statement to replace !true with true
		while(res.matches("^.*\\!true.*$") || res.matches("^.*\\!\\(true\\).*$")) {
			if(res.matches("^.*\\!true.*$")) {
				res = res.replaceAll("\\!true", "true");
			} else {
				res = res.replaceAll("\\!\\(true\\)", "true");
			}
		}
		return res;
	}
	
	public String normalize(String predicate, ArrayList<String> rcv_candidates,
			ArrayList<ArrayList<String>> args_candidates) {
		String norm = predicate;
		for (String rcv : rcv_candidates) {
			if (norm.contains(rcv)) {
				norm = norm.replaceAll(rcv, "rcv");
			}
		}

		for (ArrayList<String> args : args_candidates) {
			for (int i = 0; i < args.size(); i++) {
				if (norm.contains(args.get(i))) {
					norm = norm.replaceAll(args.get(i), "arg" + i);
				}
			}
		}

		return norm;
	}
	
	public HashMap<String, String> find_the_most_common_predicate() {
		HashMap<String, String> predicates = new HashMap<String, String>();
		for (String api : clusters.keySet()) {
			int max = 0;
			String pred = null;
			ArrayList<PredicateCluster> pcs = clusters.get(api);
			for(PredicateCluster pc : pcs) {
				if(pc.cluster.size() > max) {
					pred = pc.shortest;
				}
			}
			predicates.put(api, pred);
		}
		
		return predicates;
	}
}
