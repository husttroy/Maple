package edu.ucla.cs.utils;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.regex.Pattern;

import org.apache.commons.lang3.StringUtils;

public class SAT {
	
	private HashMap<String, String> bool_symbol_map;
	private HashMap<String, String> int_symbol_map;
	
	public SAT() {
		bool_symbol_map = new HashMap<String, String>();
		int_symbol_map = new HashMap<String, String>();
	}

	/***** Check Equivalence *****/
	
	public boolean checkEquivalence(String p1, String p2) {
		// clear previous maps
		bool_symbol_map.clear();
		int_symbol_map.clear();

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
		String query = generateEquvalenceQueryInZ3(p1_prefix, p2_prefix);
		return !isSAT(query);
	}
	
	public String generateEquvalenceQueryInZ3(String p1, String p2) {
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
	
	/***** Check Implication *****/
	
	/**
	 * Check if p1 => p2
	 * 
	 * @param p1
	 * @param p2
	 * @return
	 */
	public boolean checkImplication(String p1, String p2) {
		// clear previous maps
		bool_symbol_map.clear();
		int_symbol_map.clear();
		
		String p1_sym = symbolize(p1);
		String p2_sym = symbolize(p2);
		String p1_prefix = InfixToPrefixConvertor.infixToPrefixConvert(p1_sym);
		String p2_prefix = InfixToPrefixConvertor.infixToPrefixConvert(p2_sym);
		
		String query = generateImplicationQueryInZ3(p1_prefix, p2_prefix);
		return !isSAT(query);
	}
	
	public String generateImplicationQueryInZ3(String p1, String p2) {
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

		query += "(assert (and " + p1_smt + " (not " + p2_smt + ")))"
				+ System.lineSeparator();
		query += "(check-sat)";
		return query;
	}

	/***** General Utility *****/
	
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
		// sort the keys first based on the length to avoid the case one key is part of the other key
		Comparator<String> comparator = new Comparator<String>() {
			  public int compare(String s1, String s2) { 
			    int diff = s1.length() - s2.length();
			    if(diff > 0) {
			    	diff = -1;
			    } else if (diff < 0) {
			    	diff = 1;
			    }
			    return diff;
			  } 
			};
		Set<String> ks = new HashSet<String>(bool_symbol_map.keySet());
		ks.addAll(int_symbol_map.keySet());
		String[] sorted = ks.toArray(new String[0]);
		Arrays.sort(sorted, comparator);
		for (String s : sorted) {
			String sym;
			if(bool_symbol_map.containsKey(s)) {
				sym = bool_symbol_map.get(s);
			} else {
				sym = int_symbol_map.get(s);
			}
			expr = expr.replaceAll(Pattern.quote(s), sym);
		}
		
//		for (String s : bool_symbol_map.keySet()) {
//			String sym = bool_symbol_map.get(s);
//			expr = expr.replaceAll(Pattern.quote(s), sym);
//		}
//
//		for (String s : int_symbol_map.keySet()) {
//			String sym = int_symbol_map.get(s);
//			expr = expr.replaceAll(Pattern.quote(s), sym);
//		}

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
	protected String stripUnnecessaryParentheses(String expr) {
		String rel = expr;

		while (rel.startsWith("(") && rel.endsWith(")")) {
			rel = rel.substring(1, rel.length() - 1);
		}

		return rel;
	}
	
	public static String stripUnbalancedParentheses(String expr) {
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
}
