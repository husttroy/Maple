package edu.ucla.cs.mine;

import java.awt.Point;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;
import java.util.Stack;
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
			// keep merging the first two equivalent clusters till a fix point
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
	
	protected void optimized_merge() {
		Set<String> apis = this.clusters.keySet();
		for(String api : apis) {
			ArrayList<PredicateCluster> arr = this.clusters.get(api);
			ArrayList<PredicateCluster> newArr = optimized_merge(arr);
			this.clusters.put(api, newArr);
		}
	}
	
	

	private ArrayList<PredicateCluster> optimized_merge(
			ArrayList<PredicateCluster> arr) {
		ArrayList<PredicateCluster> newArr = new ArrayList<PredicateCluster>();
		SAT sat = new SAT();
		// keep adding each cluster in the given array to a new array
		for(PredicateCluster p1 : arr) {
			PredicateCluster eq = null;
			for(PredicateCluster p2 : newArr) {
				if (sat.checkEquivalence(p1.shortest, p2.shortest)) {
					// p1 <=> p2, merge them
					eq = p2;
					break;
				}
			}
			if(eq == null) {
				newArr.add(p1);
			} else {
				// there is an equivalent cluster
				newArr.remove(eq);
				newArr.add(new PredicateCluster(p1, eq));
			}
		}
		
		return newArr;
//		ArrayList<PredicateCluster> newArr2 = new ArrayList<PredicateCluster>();
//		// another round to check implication. 
//		for(int i = 0; i < newArr.size(); i ++) {
//			PredicateCluster p1 = newArr.get(i);
//			if(p1.shortest.equals("true")) {
//				// everything implies true 
//				newArr2.add(new PredicateCluster(p1.shortest, p1.cluster.size()));
//				continue;
//			}
//			// compare with every other cluster
//			int count = 0;
//			for(int j = 0; j < newArr.size(); j ++) {
//				if(j == i) {
//					// do not compare with itself
//				} else {
//					PredicateCluster p2 = newArr.get(j);
//					if(sat.checkImplication(p2.shortest, p1.shortest)) {
//						count += p2.cluster.size();
//					}
//				}
//			}
//			
//			newArr2.add(new PredicateCluster(p1.shortest, count + p1.cluster.size()));
// 		}
//		
//		return newArr2;
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
		optimized_merge();

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
	
	public static String condition(Set<String> vars, String predicate) {
		// replace bitwise or with logical or
		predicate = predicate.replaceAll("(?<!\\|)\\|(?!\\|)", "||");
		// replace bitwise and with logical and
		predicate = predicate.replaceAll("(?<!&|\\d\\s|\\d)&(?!(&|\\s\\d|\\d||(\\s)*[a-zA-Z0-9_]+\\)(\\s)*(\\!=|==)))", "&&");
		
		// normalize the use of assignment in the middle of a predicate as the assigned variable
		predicate = replaceAssignment(predicate);
		
		String[] arr = splitOutOfQuote(predicate);
		String res = predicate;
		for (String c : arr) {
			c = c.trim();
			if (c.isEmpty() || c.equals("(") || c.equals(")")) {
				continue;
			} else {
				c = SAT.stripUnbalancedParentheses(c);

				boolean flag = false;
				for (String var : vars) {
					if (containsVar(var, c)) {
						flag = true;
					}
				}

				if (!flag) {
					// this clause is irrelevant
					res = conditionClause(c, res);
				}
			}
		}
		
		// a && !b | a ==> a && !true, which is always evaluated to false
		// Such conditioning  is incomplete because !b should be replaced with true instead of b 
		// So we add the following replacement statement to replace !true with true
		// we also need to handle cases such as !(true && true), !(true || true), !(true || true && true), etc.
		while(res.matches("^.*true(\\s)*&&(\\s)*true.*$") || res.matches("^.*true(\\s)*\\|\\|(\\s)*true.*$") || res.matches("^.*\\!true.*$") || res.matches("^.*\\!\\(true\\).*$")) {
			if(res.matches("^.*true(\\s)*&&(\\s)*true.*$")) {
				res = res.replaceAll("true(\\s)*&&(\\s)*true", "true");
			} else if (res.matches("^.*true(\\s)*\\|\\|(\\s)*true.*$")) {
				res = res.replaceAll("true(\\s)*\\|\\|(\\s)*true", "true");
			} else if(res.matches("^.*\\!true.*$")) {
				res = res.replaceAll("\\!true", "true");
			} else {
				res = res.replaceAll("\\!\\(true\\)", "true");
			}
		}
		
		return res;
	}
	
	public static String replaceAssignment(String predicate) {
		if(predicate.matches("^.+(?<!(=|\\!|>|<))=(?!=).+$")){
			// this algorithm is based on one observation that an assignment sub-expression must be wrapped with parentheses in a boolean expression
			char[] chars = predicate.toCharArray();
			Stack<Integer> stack = new Stack<Integer>();
			int snapshot = -1;
			int assignment_index = -1;
			boolean inQuote = false;
			ArrayList<Point> ranges = new ArrayList<Point>();
			for(int i = 0; i < chars.length; i++) {
				char cur = chars[i];
				if(cur == '"' && i > 0 && chars[i-1] == '\\') {
					// count the number of backslashes
					int count = 0;
					while(i - count - 1 >= 0) {
						if(chars[i - count - 1] == '\\') {
							count ++;
						} else {
							break;
						}
					} 
					if(count % 2 == 0) {
						// escape one or more backslashes instead of this quote, end of quote
						// quote ends
						inQuote = false;
					} else {
						// escape quote, not the end of the quote
					}
				} else if(cur == '"' && !inQuote) {
					// quote starts
					inQuote = true;
				} else if(cur == '"' && inQuote) {
					// quote ends
					inQuote = false;
				} else if (inQuote) {
					// ignore any separator in quote
				} else if (cur == '=') {
					if(i + 1 < chars.length && chars[i+1] == '=') {
						// equal operator, ignore
						i++;
					} else if (i -1 >= 0 && chars[i-1] == '!') {
						// not equal operator, ignore
					} else {
						// assignment operator, stack size must be at least 1
						snapshot = stack.size();
						assignment_index = i;
					}
				} else if (cur == '(') {
					stack.push(i);
				} else if (cur == ')') {
					stack.pop();
					if(stack.size() == snapshot - 1) {
						ranges.add(new Point(assignment_index, i));
						// reset
						snapshot = -1;
						assignment_index = -1;
					}
				}
			}
			
			// remove whatever in the range list
			String rel = "";
			int cur = 0;
			for(Point p : ranges) {
				rel += predicate.substring(cur, p.x);
				cur = p.y;
			}
			
			if(cur <= predicate.length()) {
				rel += predicate.substring(cur);
			}
			
			return rel;
		} else {
			return predicate;
		}
	}

	public static String[] splitOutOfQuote(String s) {
		ArrayList<String> tokens = new ArrayList<String>();
		char[] chars = s.toCharArray();
		boolean inQuote = false;
		StringBuilder sb = new StringBuilder();
		for(int i = 0; i < chars.length; i++) {
			char cur = chars[i];
			if(cur == '"' && i > 0 && chars[i-1] == '\\') {
				// count the number of backslashes
				int count = 0;
				while(i - count - 1 >= 0) {
					if(chars[i - count - 1] == '\\') {
						count ++;
					} else {
						break;
					}
				} 
				if(count % 2 == 0) {
					// escape one or more backslashes instead of this quote, end of quote
					// quote ends
					inQuote = false;
					sb.append(cur);
				} else {
					// escape quote, not the end of the quote
					sb.append(cur);
				}
			} else if(cur == '"' && !inQuote) {
				// quote starts
				inQuote = true;
				sb.append(cur);
			} else if (cur == '\'' && i > 0 && chars[i-1] == '\\') {
				// escape single quote in quote
				sb.append(cur);
			} else if(cur == '\'' && !inQuote) {
				// single quote starts
				inQuote = true;
				sb.append(cur);
			} else if(cur == '"' && inQuote) {
				// quote ends
				inQuote = false;
				sb.append(cur);
			} else if (cur == '\'' && inQuote) {
				// single quote ends
				inQuote = false;
				sb.append(cur);
			} else if (inQuote) {
				// ignore any separator in quote
				sb.append(cur);
			} else if (cur == '&' || cur == '|'){
				// look ahead
				if (i + 1 < chars.length && chars[i+1] == cur) {
					// step forward if it is logic operator, otherwise it is a bitwise operator
					i++;
					if(sb.length() > 0) {
						// push previous concatenated chars to the array
						tokens.add(sb.toString());
						// clear the string builder
						sb.setLength(0);
					}
				} else {
					// bitwise separator
					sb.append(cur);
				}
			} else if (cur == '!') {
				// look ahead
				if (i + 1 < chars.length && chars[i+1] == '=') {
					// != operator instead of logic negation operator
					sb.append(cur);
				} else {
					if(sb.length() > 0) {
						// push previous concatenated chars to the array
						tokens.add(sb.toString());
						// clear the string builder
						sb.setLength(0);
					}
				}
			} else {
				sb.append(cur);
			}
		}
		
		// push the last token if any
		if(sb.length() > 0) {
			tokens.add(sb.toString());
		}
		
		String[] arr = new String[tokens.size()];
		for(int i = 0; i < tokens.size(); i++) {
			arr[i] = tokens.get(i);
		}
		return arr;
	}
	
	public static String normalize(String predicate, ArrayList<String> rcv_candidates,
			ArrayList<ArrayList<String>> args_candidates) {
		String norm = predicate;
		for (String rcv : rcv_candidates) {
			if (norm.contains(rcv)) {
				// cannot simply call replaceAll since some name be appear as part of other names
				//norm = norm.replaceAll(Pattern.quote(rcv), "rcv");
				norm = replaceVar(rcv, norm, "rcv");
			}
		}

		for (ArrayList<String> args : args_candidates) {
			for (int i = 0; i < args.size(); i++) {
				if (norm.contains(args.get(i))) {
					// cannot simply call replaceAll since some name be appear as part of other names
					//norm = norm.replaceAll(Pattern.quote(args.get(i)), "arg" + i);
					norm = replaceVar(args.get(i), norm, "arg" + i);
				}
			}
		}

		return norm;
	}
	
	public static boolean containsVar(String var, String clause) {
		if(clause.contains(var)) {
			boolean flag1 = false;
			boolean flag2 = false;
			// a small trick to avoid the case where a condition variable name is part of a variable name in the clause
			int ahead = clause.indexOf(var) - 1;
			int behind = clause.indexOf(var) + var.length();
			if (ahead >= 0 && ahead < clause.length()) {
				char c = clause.charAt(ahead);
				if((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
					// something contains the variable name as part of it
					flag1 = false;
				} else {
					flag1 = true;
				}
			} else {
				flag1 = true;
			}
			
			if (behind >= 0 && behind < clause.length()) {
				char c = clause.charAt(behind);
				if((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
					// something contains the variable name as part of it
					flag2 = false;
				} else {
					flag2 = true;
				}
			} else {
				flag2 = true;
			}
			
			if(flag1 && flag2) {
				return true;
			} else {
				// keep looking forward
				if(behind < clause.length()) {
					return containsVar(var, clause.substring(behind));
				} else {
					return false;
				}
			}
		} else {
			return false;
		}
	}
	
	public static String conditionClause(String clause, String predicate) {
		String res = predicate;
		String pre = "";
		// a small trick to check whether the part that matches the clause is a stand-alone clause
		while(true) {
			if(res.indexOf(clause) == -1) {
				// the clause does not exist
				break;
			} else {
				boolean flag1 = false;
				boolean flag2 = false;
				
				// look ahead and see if it reaches a clause separator, e.g., &(&), |(|), !(!=)
				int ahead = res.indexOf(clause) - 1;
				while (ahead >= 0 && ahead < res.length()) {
					char c = res.charAt(ahead);
					if(c == ' ' || c == '(') {
						// okay lets keep looking back
						ahead --;
					} else if (c == '&' || c == '!' || c == '|'){
						flag1 = true;
						break;
					} else {
						break;
					}
				}
				
				if(ahead == -1) {
					// this clause appear in the beginning
					flag1 = true;
				}
				
				int behind = res.indexOf(clause) + clause.length();
				while (behind >= 0 && behind < res.length()) {
					char c = res.charAt(behind);
					if(c == ' ' || c == ')') {
						// okay lets keep looking behind
						behind ++;
					} else if (c == '&' || c == '|'){
						flag2 = true;
						break;
					} else if (c == '!' && behind + 1 < res.length() && res.charAt(behind + 1) != '=') {
						flag2 = true;
						break;
					} else {
						break;
					}
				}
				
				if(behind == res.length()) {
					// this clause appears in the end
					flag2 = true;
				}
				
				if(flag1 && flag2) {
					// stand-alone clause
					String sub1 = res.substring(0, res.indexOf(clause));
					String sub2 = res.substring(res.indexOf(clause) + clause.length());
					return pre + sub1 + "true" + sub2;
				} else {
					// keep searching
					pre = res.substring(0, behind);
					res = res.substring(behind);
				}
			}
		}
		
		return predicate;
	}
	
	public static String replaceVar(String var, String predicate, String substitute) {
		if(!containsVar(var, predicate)) {
			return predicate;
		}
		
		boolean flag1 = false;
		boolean flag2 = false;
		// a small trick to avoid the case where a condition variable name is part of a variable name in the clause
		int ahead = predicate.indexOf(var) - 1;
		int behind = predicate.indexOf(var) + var.length();
		
		if (ahead >= 0 && ahead < predicate.length()) {
			char c = predicate.charAt(ahead);
			if((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
				// something contains the variable name as part of it
				flag1 = false;
			} else {
				flag1 = true;
			}
		} else {
			flag1 = true;
		}
		
		if (behind >= 0 && behind < predicate.length()) {
			char c = predicate.charAt(behind);
			if((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
				// something contains the variable name as part of it
				flag2 = false;
			} else {
				flag2 = true;
			}
		} else {
			flag2 = true;
		}
		

		String sub1 = predicate.substring(0, ahead + 1);
		String sub2 = predicate.substring(behind);
		if(flag1 && flag2) {
			// replace it
			return sub1 + substitute + replaceVar(var, sub2, substitute);
		} else {
			// keep looking forward
			return sub1 + var + replaceVar(var, sub2, substitute);
		}
	}
	
	public HashMap<String, HashMap<String, Integer>> find_the_most_common_predicate(int threshold) {
		HashMap<String, HashMap<String, Integer>> predicates = new HashMap<String, HashMap<String, Integer>>();
		for (String api : clusters.keySet()) {
			HashMap<String, Integer> ps = new HashMap<String, Integer>();
			ArrayList<PredicateCluster> pcs = clusters.get(api);
			for(PredicateCluster pc : pcs) {
				if(pc.cluster.size() > threshold) {
					ps.put(pc.shortest, pc.cluster.size());
				}
			}
			predicates.put(api, ps);
		}
		
		return predicates;
	}
}
