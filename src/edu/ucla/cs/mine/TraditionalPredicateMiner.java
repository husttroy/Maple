package edu.ucla.cs.mine;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang3.StringUtils;

import edu.ucla.cs.utils.ProcessUtils;

public class TraditionalPredicateMiner extends PredicatePatternMiner {
	static final Pattern METHOD_CALL = Pattern
			.compile("((new )?[a-zA-Z0-9_]+)\\(((.+),)*\\)");

	String path;
	String sequence_path;

	public TraditionalPredicateMiner(ArrayList<String> pattern,
			String raw_output, String seq) {
		super(pattern);
		this.path = raw_output;
		this.sequence_path = seq;
	}

	@Override
	protected void loadAndFilterPredicate() {
		// find API call sequences that follow the pattern
		SequencePatternVerifier pv = new SequencePatternVerifier(pattern);
		pv.verify(sequence_path);

		// read the full output of the traditional analysis
		File output = new File(path);
		try (BufferedReader br = new BufferedReader(new FileReader(output))) {
			String line;
			while ((line = br.readLine()) != null) {
				if(!line.startsWith("results[")) {
					continue;
				}
				String key = line.substring(line.indexOf("[") + 1,
						line.indexOf("][SEQ]"));
				key = key.replaceAll("\\!", " ** ");
				if (pv.support.containsKey(key)) {
					// this sequence follows the pattern
					String seq = line.substring(line.indexOf("] =") + 3).trim();
					if(seq.contains("?")) {
						// cannot handle conditional expressions
						continue;
					}
					
					ArrayList<String> arr = splitByArrow(seq);

					HashMap<String, ArrayList<String>> map = new HashMap<String, ArrayList<String>>();
					// skip the first element because it is empty string
					for(String str : arr) {
						str = str.trim();
						// strip off the close parentheses at the end (if any)
						if (str.endsWith("}")) {
							while (str.endsWith("}")) {
								str = str.substring(0, str.lastIndexOf("}"))
										.trim();
							}
						}

						// strip off the control flow at the end (if any)
						while (str.endsWith("} ELSE {")
								|| str.endsWith("} CATCH {")
								|| str.endsWith("} FINALLY {")) {
							str = str.substring(0, str.lastIndexOf('}') + 1);
							while (str.endsWith("}")) {
								str = str.substring(0, str.lastIndexOf("}"))
										.trim();
							}
						}

						// skip if it is empty or it is a control-flow construct
						if (str.isEmpty() || str.equals("IF {")
								|| str.equals("ELSE {") || str.equals("TRY {")
								|| str.equals("CATCH {")
								|| str.equals("LOOP {")
								|| str.equals("FINALLY {")) {
							continue;
						}

						// split by @
						String[] ss = splitByAt(str);
						String predicate = null;
						String item = ss[0];
						if(ss[1].trim().isEmpty()) {
							predicate = "true";
						} else {
							predicate = ss[1];
						}
						
						// pre-check to avoid unnecessary pattern matching for
						// the performance purpose
						if (!item.contains("(") || !item.contains(")")) {
							continue;
						}

						// extract predicates for each method call in this
						// expression
						HashMap<String, ArrayList<String>> predicates = propagatePredicates(
								item.trim(), predicate);

						// aggregate the predicates with those from previous
						// sequences
						for (String name : predicates.keySet()) {
							if (map.containsKey(name)) {
								map.get(name).addAll(predicates.get(name));
							} else {
								map.put(name, predicates.get(name));
							}
						}
					}

					this.predicates.put(key, map);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public String[] splitByAt(String s) {
		ArrayList<String> ss = new ArrayList<String>();
		String[] arr = s.split("@");
		int index = 0;
		for(int i = 0; i < arr.length; i++) {
			String item = arr[i];
			if(!isInQuote(s, index)) {
				ss.add(item);
			} else {
				String last = ss.get(ss.size() - 1);
				ss.remove(ss.size() - 1);
				ss.add(last + "@" + item);
			}
			index += item.length() + 1;
		}
		
		if(ss.size() == 1) {
			ss.add("true");
		}
		
		String[] arr2 = new String[ss.size()];
		return ss.toArray(arr2);
	}
	
	public ArrayList<String> splitByArrow(String s) {
		ArrayList<String> ss = new ArrayList<String>();
		String[] arr = s.split("->");
		int index = 0;
		for(int i = 0; i < arr.length; i++) {
			String item = arr[i];
			if(!isInQuote(s, index)) {
				ss.add(item);
			} else {
				String last = ss.get(ss.size() - 1);
				ss.remove(ss.size() - 1);
				ss.add(last + "->" + item);
			}
			index += item.length() + 2;
		}
		
		return ss;
	}

	public HashMap<String, ArrayList<String>> propagatePredicates(String expr,
			String predicate) {
		HashMap<String, ArrayList<String>> predicates = new HashMap<String, ArrayList<String>>();
		Matcher m = METHOD_CALL.matcher(expr);
		while (m.find()) {
			String apiName = m.group(1);
			
			// first check about whether there are chained or nested method calls in the "arguments" (not real arguments due to inaccurate regex)
			String args = m.group(3);
			ArrayList<String> arguments = new ArrayList<String>();
			if (args != null) {
				String rest = null;
				// check whether this is a chained method call by checking
				// whether the argument is balanced
				if (!ProcessUtils.isBalanced(args)) {
					// this is a call chain
					// the regex cannot handle the method calls properly if one
					// method call
					// after the first one in the chain contains arguments
					// the following method calls with arguments will be
					// considered as the
					// argument of the first one
					int position = ProcessUtils
							.findFirstUnbalancedCloseParenthesis(args);
					if (position == -1) {
						// something goes wrong, return empty list
						return new HashMap<String, ArrayList<String>>();
					} else {
						// adjust the string of the argument list
						String newArgs = args.substring(0, position);
						if (position + 2 <= args.length()) {
							rest = args.substring(position + 2) + ")";
						}
						args = newArgs;
					}
				}

				// split arguments
				// this has to be done here because we do not want previous
				// argument to be part of the receiver of API calls in the next
				// argument
				arguments = getArguments(args);
				for (String arg : arguments) {
					HashMap<String, ArrayList<String>> p2 = propagatePredicates(
							arg, predicate);
					// aggregate
					for (String name : p2.keySet()) {
						if (predicates.containsKey(name)) {
							predicates.get(name).addAll(p2.get(name));
						} else {
							predicates.put(name, p2.get(name));
						}
					}
				}

				// then process the rest of the API calls in the chain (if any)
				if (rest != null) {
					HashMap<String, ArrayList<String>> p3 = propagatePredicates(
							rest, predicate);
					// aggregate
					for (String name : p3.keySet()) {
						if (predicates.containsKey(name)) {
							predicates.get(name).addAll(p3.get(name));
						} else {
							predicates.put(name, p3.get(name));
						}
					}
				}
			}

			if (!pattern.contains(apiName)) {
				// skip if the API call does not appear in the sequence pattern
				continue;
			}

			String receiver = getReceiver(expr, apiName);
			
			HashSet<String> relevant_elements = new HashSet<String>();
			if (receiver != null && !receiver.isEmpty()) {
				relevant_elements.add(receiver);
			}
			relevant_elements.addAll(arguments);

			// remove irrelevant clauses
			String conditioned_predicate;
			if(!predicate.equals("true")) {
				conditioned_predicate = condition(relevant_elements,predicate);
			} else {
				conditioned_predicate = "true";
			}
					
			// normalize names
			// declare temporary variables to fit the API
			ArrayList<String> temp1 = new ArrayList<String>();
			if (receiver != null) {
				temp1.add(receiver);
			}
			ArrayList<ArrayList<String>> temp2 = new ArrayList<ArrayList<String>>();
			temp2.add(arguments);

			String normalized_predicate;
			if(!conditioned_predicate.equals("true")) {
				normalized_predicate = normalize(conditioned_predicate,
						temp1, temp2);
			} else {
				normalized_predicate = "true";
			}

			if (normalized_predicate.equals("!(rcv.countTokens()==1) && true && !(rcv.countTokens()<) && true")) {
				System.out.println("oops");
			}
			ArrayList<String> value;
			if (predicates.containsKey(apiName)) {
				value = predicates.get(apiName);
			} else {
				value = new ArrayList<String>();
			}
			value.add(normalized_predicate);
			predicates.put(apiName, value);
		}

		return predicates;
	}

	public String getReceiver(String expr, String apiName) {
		String receiver = null;
		if (!apiName.startsWith("new ")) {
			// make sure this is not a call to class constructor since class
			// constructors do not have receivers
			int index = expr.indexOf(apiName);
			String sub = expr.substring(0, index);
			if (sub.endsWith(".")) {
				// make sure it is not a call to local method since local method
				// calls also do not have receivers
				if (sub.startsWith("return ")) {
					// return statement
					receiver = sub.substring(7, sub.length() - 1);
				} else if (sub.matches("[a-zA-Z0-9_]+=.+")) {
					// assignment statement
					receiver = sub.substring(sub.indexOf("=") + 1,
							sub.length() - 1);
				} else {
					// regular method call
					receiver = sub.substring(0, sub.length() - 1);
				}

				// strip off any type casting of the return value before the receiver
				// but be careful and do not strip off the type casting in the receiver
				receiver = receiver.trim();
				if (receiver.startsWith("(") && !receiver.endsWith(")")) {
					receiver = receiver.substring(receiver.indexOf(')') + 1);
					receiver = receiver.trim();
				}
			}
		}
		return receiver;
	}

//	public ArrayList<String> getArguments(String args) {
//		ArrayList<String> list = new ArrayList<String>();
//		int stack = 0;
//		String[] ss = args.split(",");
//		String arg = "";
//		for (String s : ss) {
//			int open = StringUtils.countMatches(s, "(");
//			int close = StringUtils.countMatches(s, ")");
//			stack += open - close;
//			if (stack != 0) {
//				arg += s + ",";
//			} else {
//				arg += s;
//				if (!arg.isEmpty()) {
//					list.add(arg);
//				}
//				arg = "";
//			}
//		}
//		return list;
//	}
	
	public ArrayList<String> getArguments(String args) {
		ArrayList<String> list = new ArrayList<String>();
		boolean inQuote = false;
		int stack = 0;
		StringBuilder sb = new StringBuilder();
		char[] chars = args.toCharArray();
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
					// escape single quote, not the end of the quote
					sb.append(cur);
				}
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
			} else if (cur == '(' && !inQuote) {
				// look behind to check if this is a method call
				sb.append(cur);
				stack ++;
			} else if (cur == ')' && !inQuote) {
				sb.append(cur);
				stack --;
			} else if (inQuote || stack != 0) {
				// ignore any separator in quote or in a method call
				sb.append(cur);
			} else if (cur == ',' && !inQuote && stack == 0){
				if(sb.length() > 0) {
					list.add(sb.toString());
					sb.setLength(0);
				} else {
					sb.append(cur);
				}
			} else {
				sb.append(cur);
			}
		}
		
		// push the last token if any
		if(sb.length() > 0) {
			list.add(sb.toString());
		}
		
		return list;
	}

	public static void main(String[] args) {
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("nextToken");
		String path = "/home/troy/research/BOA/Maple/example/StringTokenizer.nextToken/large-sequence.txt";
		String sequence_path = "/home/troy/research/BOA/Maple/example/StringTokenizer.nextToken/large-output.txt";
		TraditionalPredicateMiner pm = new TraditionalPredicateMiner(pattern,
				path, sequence_path);
		pm.process();
	}
}
