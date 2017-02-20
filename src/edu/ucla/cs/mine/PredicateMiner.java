package edu.ucla.cs.mine;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
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

public class PredicateMiner {
	HashMap<String, HashMap<String, ArrayList<String>>> predicates; // id ->
																	// predicates
																	// (filtered
																	// +
																	// normalized)
	HashMap<String, HashMap<String, ArrayList<String>>> arguments; // id ->
																	// arguments
	HashMap<String, HashMap<String, ArrayList<String>>> receivers; // id ->
																	// receivers
	ArrayList<String> pattern;
	HashMap<String, ArrayList<PredicateCluster>> clusters; // api -> clusters of
															// predicates

	final String predicate_path = "/home/troy/research/BOA/Slicer/example/predicate.txt";
	final String sequence_path = "/home/troy/research/BOA/Slicer/example/output.txt";
	final String argument_path = "/home/troy/research/BOA/Slicer/example/argument.txt";
	final String receiver_path = "/home/troy/research/BOA/Slicer/example/receiver.txt";
	final String logicSeparator = "&&|\\|\\|";

	public PredicateMiner(ArrayList<String> pattern) {
		predicates = new HashMap<String, HashMap<String, ArrayList<String>>>();
		arguments = new HashMap<String, HashMap<String, ArrayList<String>>>();
		receivers = new HashMap<String, HashMap<String, ArrayList<String>>>();
		this.pattern = new ArrayList<String>();
		for (String p : pattern) {
			if (p.contains("{") || p.contains("}")) {
				continue;
			} else {
				this.pattern.add(p);
			}
		}
		clusters = new HashMap<String, ArrayList<PredicateCluster>>();
	}

	/**
	 * 1. find all method call sequences that satisfy the given pattern 2. for
	 * each API call sequence, find the arguments and receiver of each API in
	 * the pattern 3. for each predicate, filter out those clauses that do not
	 * include these arguments and receiver 4. initially cluster identical
	 * predicates 5. for every two clusters, merge them if they are semantically
	 * equivalent using z3 6. keep merging until a fix point
	 */
	public void process() {
		// find API call sequences that follow the pattern
		PatternVerifier pv = new PatternVerifier(pattern);
		pv.verify(sequence_path);

		// load arguments and receivers
		loadArugmentInfo(pv.support.keySet());
		loadReceiverInfo(pv.support.keySet());

		// load and filter predicates, and normalize variable names
		loadAndFilterPredicate(pv.support.keySet());

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

	private void merge() {
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

			if (e.isEmpty()) {
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

	private String stripUnbalancedParentheses(String expr) {
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

	private void setup() {
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

	private void loadAndFilterPredicate(Set<String> ref) {
		File output = new File(predicate_path);
		try (BufferedReader br = new BufferedReader(new FileReader(output))) {
			String line;
			while ((line = br.readLine()) != null) {
				if (line.startsWith("conds[")) {
					String id = line.substring(line.indexOf("[") + 1,
							line.indexOf("] =")).trim();
					if (!ref.contains(id)) {
						continue;
					}

					HashMap<String, ArrayList<String>> map = new HashMap<String, ArrayList<String>>();

					String tmp = line.substring(line.indexOf("] =") + 3).trim();
					String[] records = tmp.split(";;;");
					for (String record : records) {
						String api = record.split("::")[0];
						if (!pattern.contains(api)) {
							continue;
						}

						HashSet<String> relevant_elements = new HashSet<String>();
						ArrayList<String> rcv_candidates = find_receivers(id,
								api);
						relevant_elements.addAll(rcv_candidates);
						ArrayList<ArrayList<String>> args_candidates = find_arguments(
								id, api);
						for (ArrayList<String> a : args_candidates) {
							relevant_elements.addAll(a);
						}

						String conds = record.split("::")[1];

						ArrayList<String> arr = new ArrayList<String>();

						String[] ss = conds.split("\\*\\*\\*");
						for (String s : ss) {
							boolean flag = false;
							for (String var : relevant_elements) {
								if (s.contains(var)) {
									flag = true;
									break;
								}
							}

							if (flag) {
								// condition on the relevant variables (i.e.,
								// receivers, arguments)
								// in order to compute the weakest precondition
								s = condition(relevant_elements, s);
								// normalize names
								s = normalize(s, rcv_candidates,
										args_candidates);
								arr.add(s);
							}
						}

						if (arr.isEmpty()) {
							arr.add("true");
						}

						map.put(api, arr);
					}

					for (String api : pattern) {
						if (!map.containsKey(api)) {
							// no predicate for this api => the precondition for
							// this api is true
							ArrayList<String> arr = new ArrayList<String>();
							arr.add("true");
							map.put(api, arr);
						}
					}

					predicates.put(id, map);
				}
			}
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
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

	public String condition(Set<String> vars, String predicate) {
		String[] arr = predicate.split("&&|\\|\\||\\!(?!=)");
		String res = predicate;
		for (String c : arr) {
			c = c.trim();
			if (c.isEmpty()) {
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

		return res.replaceAll("\\!(\\(*)true(\\)*)", "true");
	}

	private ArrayList<String> find_receivers(String id, String api) {
		HashMap<String, ArrayList<String>> all_rcvs = this.receivers.get(id);

		ArrayList<String> vars = new ArrayList<String>();
		ArrayList<String> rcvs = all_rcvs.get(api);
		for (String rcv : rcvs) {
			if (rcv.startsWith("v::")) {
				vars.add(rcv.substring(3));
			}
		}

		return vars;
	}

	private ArrayList<ArrayList<String>> find_arguments(String id, String api) {
		HashMap<String, ArrayList<String>> all_args = this.arguments.get(id);

		ArrayList<ArrayList<String>> vars = new ArrayList<ArrayList<String>>();
		ArrayList<String> argss = all_args.get(api);
		for (String args : argss) {
			String[] arr = args.split(",");
			ArrayList<String> temp = new ArrayList<String>();
			for (int i = 0; i < arr.length; i++) {
				String arg = arr[i];
				if (arg.startsWith("v::")) {
					temp.add(arg.substring(3));
				}
			}
			vars.add(temp);
		}

		return vars;
	}

	private void loadArugmentInfo(Set<String> ref) {
		File output = new File(argument_path);
		try (BufferedReader br = new BufferedReader(new FileReader(output))) {
			String line;
			while ((line = br.readLine()) != null) {
				if (line.startsWith("margs[")) {
					String id = line.substring(line.indexOf("[") + 1,
							line.indexOf("] =")).trim();
					if (!ref.contains(id)) {
						// this sequence does not follow the given pattern
						continue;
					}

					String tmp = line.substring(line.indexOf("] =") + 3).trim();
					String[] ss = tmp.split("@@");

					HashMap<String, ArrayList<String>> call_args_map = new HashMap<String, ArrayList<String>>();
					for (int i = 0; i < ss.length; i++) {
						String name = ss[i].split("->")[0];
						String calls = ss[i].split("->")[1];

						String[] arr = calls.split(";;;");
						ArrayList<String> al = new ArrayList<String>();
						for (int j = 0; j < arr.length; j++) {
							String args = arr[j];
							al.add(args);
						}
						call_args_map.put(name, al);
					}

					arguments.put(id, call_args_map);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private void loadReceiverInfo(Set<String> ref) {
		File output = new File(receiver_path);
		try (BufferedReader br = new BufferedReader(new FileReader(output))) {
			String line;
			while ((line = br.readLine()) != null) {
				if (line.startsWith("receivers[")) {
					String id = line.substring(line.indexOf("[") + 1,
							line.indexOf("] =")).trim();
					if (!ref.contains(id)) {
						// this sequence does not follow the given pattern
						continue;
					}

					String tmp = line.substring(line.indexOf("] =") + 3).trim();
					String[] ss = tmp.split("@@");

					HashMap<String, ArrayList<String>> call_receivers_map = new HashMap<String, ArrayList<String>>();
					for (int i = 0; i < ss.length; i++) {
						String call = ss[i].split("->")[0];
						String vars = ss[i].split("->")[1];

						String[] arr = vars.split(";;;");
						ArrayList<String> rcvs = new ArrayList<String>();
						for (int j = 0; j < arr.length; j++) {
							String receiver = arr[j];
							rcvs.add(receiver);
						}
						call_receivers_map.put(call, rcvs);
					}

					receivers.put(id, call_receivers_map);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void print() {
		for (String key : predicates.keySet()) {
			System.out.println(key);
			System.out.println(predicates.get(key));
		}
	}

	public static void main(String[] args) {
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("IF {");
		pattern.add("createNewFile");
		pattern.add("}");
		PredicateMiner pm = new PredicateMiner(pattern);
		pm.process();
		// pm.print();
	}
}
