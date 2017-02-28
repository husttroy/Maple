package edu.ucla.cs.mine;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.regex.Pattern;

import org.apache.commons.lang3.StringUtils;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multiset;

import edu.ucla.cs.model.PredicateCluster;
import edu.ucla.cs.utils.FileUtils;
import edu.ucla.cs.utils.InfixToPrefixConvertor;

public abstract class PredicateMiner {
	// id -> predicates (filtered + normalized)
	HashMap<String, HashMap<String, ArrayList<String>>> predicates; 
	ArrayList<String> pattern;
	// api -> clusters of predicates
	HashMap<String, ArrayList<PredicateCluster>> clusters;
	
	public PredicateMiner (ArrayList<String> pattern) {
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
		for (int i = 0; i < arr.size(); i++) {
			PredicateCluster pc1 = arr.get(i);
			for (int j = i + 1; j < arr.size(); j++) {
				PredicateCluster pc2 = arr.get(j);
				if (checkEquivalence(pc1, pc2)) {
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

	private HashMap<String, String> bool_symbol_map = new HashMap<String, String>();
	private HashMap<String, String> int_symbol_map = new HashMap<String, String>();

	public boolean checkEquivalence(PredicateCluster pc1, PredicateCluster pc2) {
		// clear previous maps
		bool_symbol_map.clear();
		int_symbol_map.clear();

		String p1 = pc1.shortest;
		String p2 = pc2.shortest;

		// replace variable names and function calls with boolean and integer
		// symbols consistently. because Z3 does not support function calls and
		// we also need to know the type of each variables and subexpressions.
		String p1_sym = symbolize(p1);
		String p2_sym = symbolize(p2);

		// convert infix expressions to prefix expressions because Z3 encodes
		// expression in prefix order
		String p1_prefix = InfixToPrefixConvertor.infixToPrefixConvert(p1_sym);
		String p2_prefix = InfixToPrefixConvertor.infixToPrefixConvert(p2_sym);

		// For expression A and B, encode them in the format of (A && !B) || (!A && B) in Z3 to
		// check semantic equivalence
		String query = generateZ3Query(p1_prefix, p2_prefix);
		return !isSAT(query);
	}

	public boolean isSAT(String query) {
		// write query to a temporary file
		FileUtils.writeStringToFile(query, "./temp.z3");

		// run Z3
		String output = "";
		try {
			Process p = Runtime.getRuntime().exec("z3 ./temp.z3");
			BufferedReader stdInput = new BufferedReader(new InputStreamReader(
					p.getInputStream()));

			String s = null;
			while ((s = stdInput.readLine()) != null) {
				output += s;
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

		boolean result;
		if (output.equals("sat")) {
			result = true;
		} else if (output.equals("unsat")) {
			result = false;
		} else {
			result = false;
			System.err.println("Z3 Formating error!");
			// delete the temporary file
			FileUtils.delete("./temp.z3");
			System.exit(-1);
		}

		// delete the temporary file
		FileUtils.delete("./temp.z3");

		return result;
	}

	public String generateZ3Query(String p1, String p2) {
		String p1_smt = encodeToSMTLibStandard(p1);
		String p2_smt = encodeToSMTLibStandard(p2);

		String query = "";
		// dump boolean symbols to a hashset to remove duplicated symbols
		HashSet<String> bool_sym_set = new HashSet<String>(bool_symbol_map.values());
		// declare boolean symbols in Z3
		for (String sym : bool_sym_set) {
			query += "(declare-const " + sym + " Bool)"
					+ System.lineSeparator();
		}

		// dump integer symbols to a hashset to remove duplicated symbols
		HashSet<String> int_sym_set = new HashSet<String>(int_symbol_map.values());
		for (String sym : int_sym_set) {
			query += "(declare-const " + sym + " Int)" + System.lineSeparator();
		}

		query += "(assert (or (and " + p1_smt + " (not " + p2_smt + ")) (and (not " + p1_smt + ") " + p2_smt + ")))"
				+ System.lineSeparator();
		query += "(check-sat)";
		return query;
	}

	private String encodeToSMTLibStandard(String expr) {
		String rel = expr;
		// replace && with and
		rel = rel.replaceAll("&&", "and");
		// replace || with or
		rel = rel.replaceAll("\\|\\|", "or");
		// replace ! with not
		rel = rel.replaceAll("\\!(?!=)", "not");
		// replace == with =
		rel = rel.replaceAll("==", "=");
		// replace / with div
		rel = rel.replaceAll("\\/", "div");
		return rel;
	}

	/**
	 * 
	 * Support conditional expression with logic operators (i.e., !, &&, ||) and
	 * arithmetic operators (i.e., *, /, +, -) We treat function calls and
	 * objects as integers. Specifically, null is encoded as 0. For example,
	 * rcv.getA() != null is encoded as X != 0.
	 * 
	 * @param expr
	 * @return
	 */
	public String symbolize(String expr) {
		// first tokenize this expression by logic operators
		String[] arr = expr.split("&&|\\|\\||\\!(?!=)");
		for (String e : arr) {
			e = e.trim();

			if (e.isEmpty() || e.equals("(") || e.equals(")")) {
				continue;
			} else {
				e = stripUnbalancedParentheses(e);
			}

			if (e.contains("+") || e.contains("-") || e.contains("*")
					|| e.contains("/") || e.contains(">") || e.contains("<")
					|| e.contains(">=") || e.contains("<=") || e.contains("==")
					|| e.contains("!=")) {
				// this subexpression contains arithmetic operators.
				// separator order matters!!!
				String[] arr2 = e.split("\\+|-|\\*|\\/|>=|<=|>|<|==|\\!=");

				// treat these sub-subexpressions as integers
				for (String sub : arr2) {
					sub = sub.trim();
					// strip unbalanced parentheses
					sub = stripUnbalancedParentheses(sub);

					if (sub.matches("^\\d+$")) {
						continue;
					} else if (sub.matches("^(\\(+)\\d+(\\(+)")) {
						// replace these literals with unnecessary parentheses
						// with themselves
						String temp = stripUnnecessaryParentheses(sub);
						expr = expr.replaceAll(Pattern.quote(sub), temp);
						continue;
					} else if (sub.matches("^null$")) {
						expr = expr.replaceAll("null", "0");
						continue;
					}

					if (int_symbol_map.containsKey(sub)) {
						continue;
					} else {
						String temp = stripUnnecessaryParentheses(sub);
						if (int_symbol_map.containsKey(temp)) {
							String sym = int_symbol_map.get(temp);
							int_symbol_map.put(sub, sym);
						} else {
							String sym = "i" + int_symbol_map.size();
							int_symbol_map.put(sub, sym);
							if (!temp.equals(sub)) {
								// parentheses have been stripped off, also put the
								// stripped off version into the map
								int_symbol_map.put(temp, sym);
							}
						}
					}
				}

			} else {

				if (e.matches("^true$") || e.matches("^false$")) {
					continue;
				} else if (e.matches("^(\\(+)true(\\)+)$")
						|| e.matches("^(\\(+)false(\\)+)$")) {
					// replace these literals with unnecessary parentheses with
					// themselves
					String temp = stripUnnecessaryParentheses(e);
					expr = expr.replaceAll(Pattern.quote(e), temp);
					continue;
				}

				// this subexpression can be variable names, function calls,
				// etc. Check if this subexpression has already had a symbol in
				// the map.
				if (bool_symbol_map.containsKey(e)) {
					continue;
				} else {
					String temp = stripUnnecessaryParentheses(e);
					if (bool_symbol_map.containsKey(temp)) {
						String sym = bool_symbol_map.get(temp);
						bool_symbol_map.put(e, sym);
					} else {
						String sym = "b" + bool_symbol_map.size();
						bool_symbol_map.put(e, sym);
						if (!temp.equals(e)) {
							// parentheses have been stripped off, also put the
							// stripped off version into the map
							bool_symbol_map.put(temp, sym);
						}
					}
				}
			}
		}

		// replace function calls and variable names with symbols
		for (String s : bool_symbol_map.keySet()) {
			String sym = bool_symbol_map.get(s);
			expr = expr.replaceAll(Pattern.quote(s), sym);
		}

		for (String s : int_symbol_map.keySet()) {
			String sym = int_symbol_map.get(s);
			expr = expr.replaceAll(Pattern.quote(s), sym);
		}

		return expr;
	}

	/**
	 * 
	 * Strip off unnecessary parentheses, we assume that the number of open
	 * parentheses and close parentheses are the same
	 * 
	 * @param expr
	 * @return
	 */
	private String stripUnnecessaryParentheses(String expr) {
		String rel = expr;

		if (expr.matches("^(\\()+[a-zA-Z0-9_\\.]+(\\))+$")) {
			int count = StringUtils.countMatches(expr, '(');
			for (int i = 0; i < count; i++) {
				rel = rel.substring(1, rel.length() - 1);
			}
		}

		return rel;
	}

	protected String stripUnbalancedParentheses(String expr) {
		String rel = expr;

		int left = StringUtils.countMatches(rel, "(");
		int right = StringUtils.countMatches(rel, ")");

		// remove extra parentheses in each clause
		if (left > right && rel.startsWith("(")) {
			for (int i = 0; i < left - right; i++) {
				if (rel.startsWith("(")) {
					rel = rel.substring(1);
				}
			}
		} else if (left < right && rel.endsWith(")")) {
			for (int i = 0; i < right - left; i++) {
				if (rel.endsWith(")")) {
					rel = rel.substring(0, rel.length() - 1);
				}
			}
		}

		return rel;
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
				c = stripUnbalancedParentheses(c);

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
}
