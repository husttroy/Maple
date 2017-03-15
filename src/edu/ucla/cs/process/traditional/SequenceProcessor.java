package edu.ucla.cs.process.traditional;

import java.util.ArrayList;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.ucla.cs.model.Method;

public class SequenceProcessor extends ProcessStrategy {
	// match < and > in API names to handle constructors of parameterized types
	static final Pattern METHOD_CALL = Pattern
			.compile("((new )?[a-zA-Z0-9_<>]+)\\(((.+),)*\\)");

	@Override
	void process(String line) {
		Method m = getMethodInstance(line);
		buildSequenceMap(m, line);
	}

	protected void buildSequenceMap(Method method, String line) {
		String s = line.substring(line.indexOf("] =") + 3).trim();
		String[] ss = s.split("->");
		// skip the first element because it is empty string
		for (int i = 1; i < ss.length; i++) {
			if (ss[i].contains("}")) {
				String str = ss[i].trim();
				while (str.contains("}")) {
					String sub1 = str.substring(0, str.indexOf("}")).trim();
					if (!sub1.isEmpty()) {
						method.seq.addAll(extractItems(sub1));
					}
					method.seq.add("}");
					str = str.substring(str.indexOf("}") + 1);
				}

				if (!str.isEmpty()) {
					method.seq.addAll(extractItems(str));
				}
			} else {
				method.seq.addAll(extractItems(ss[i].trim()));
			}
		}
	}

	public ArrayList<String> extractItems(String expr) {
		ArrayList<String> items = new ArrayList<String>();

		// check if it is a control-flow construct
		String s = expr.trim();
		if (s.equals("IF {") || s.equals("ELSE {") || s.equals("TRY {")
				|| s.equals("CATCH {") || s.equals("LOOP {")
				|| s.equals("FINALLY {")) {
			items.add(s);
			return items;
		}

		String[] ss = s.split("@");
		// we assume the last @ splits the statement and its precondition
		// but we will run into trouble if there is an @ in the precondition
		if (ss.length == 1) {
			s = ss[0];
		} else {
			s = ss[ss.length - 2];
		}

		// pre-check to avoid unnecessary pattern matching for the performance
		// purpose
		if (s.contains("(") && s.contains(")")) {
			// extract method calls
			return extractMethodCalls(s);
		} else {
			// no method call, skip
			return items;
		}
	}

	private ArrayList<String> extractMethodCalls(String expr) {
		ArrayList<String> items = new ArrayList<String>();

		final ExecutorService service = Executors.newSingleThreadExecutor();
		try {
			final Future<Object> f = service.submit(() -> {
				Matcher m = METHOD_CALL.matcher(expr);
				while (m.find()) {
					String apiName = m.group(1);
					String args = m.group(3);
					String rest = null;
					if (args != null) {
						// check whether this is a chained method call by checking whether the argument is balanced
						if(!isBalanced(args)) {
							// this is a call chain
							// the regex cannot handle the method calls properly if one method call
							// after the first one in the chain contains arguments
							// the following method calls with arguments will be considered as the
							// argument of the first one
							int position = findFirstUnbalancedCloseParenthesis(args);
							if(position == -1) {
								// something goes wrong, return empty list
								return new ArrayList<String>();
							} else {
								// adjust the string of the argument list
								String newArgs = args.substring(0, position);
								if(position + 2 <= args.length()) {
									rest = args.substring(position + 2) + ")";
								}
								args = newArgs;
							}
						}
						
						// this api call has arguments
						ArrayList<String> apis2 = extractMethodCalls(args);
						items.addAll(apis2);
						
						// the add this API call
						items.add(apiName);
						
						// then process the rest of the API calls in the chain (if any)
						if(rest != null) {
							ArrayList<String> apis3 = extractMethodCalls(rest);
							items.addAll(apis3);
						}
					} else {
						items.add(apiName);
					}
				}
				return "yes";
			});

			f.get(1, TimeUnit.SECONDS);
		} catch (final TimeoutException e) {
			// catastrophic backtracking
			System.out.println("Regex runs more than 1 second! Ignore it!");
		} catch (final Exception e) {
			throw new RuntimeException(e);
		} finally {
			service.shutdown();
		}

		return items;
	}
	
	public boolean isBalanced(String expr) {
		boolean inQuote = false;
		int parentheses = 0;
		char[] chars = expr.toCharArray();
		for(int i = 0; i < chars.length; i++) {
			char cur = chars[i];
			if(cur == '"' && i > 0 && chars[i-1] == '\\') {
				// escape, ignore this quote
			} else if(cur == '"' && !inQuote) {
				inQuote = true;
			} else if(cur == '"' && inQuote) {
				inQuote = false;
			} else if (inQuote) {
				// ignore all parentheses in quote
			} else if (cur == '(') {
				parentheses ++;
			} else if (cur == ')') {
				parentheses --;
				if(parentheses < 0) {
					return false;
				}
			}
		}
		
		return parentheses == 0;
	}
	
	public int findFirstUnbalancedCloseParenthesis(String expr) {
		boolean inQuote = false;
		int parentheses = 0;
		char[] chars = expr.toCharArray();
		for(int i = 0; i < chars.length; i++) {
			char cur = chars[i];
			if(cur == '"' && i > 0 && chars[i-1] == '\\') {
				// escape, ignore this quote
			} else if(cur == '"' && !inQuote) {
				inQuote = true;
			} else if(cur == '"' && inQuote) {
				inQuote = false;
			} else if (inQuote) {
				// ignore all parentheses in quote
			} else if (cur == '(') {
				parentheses ++;
			} else if (cur == ')') {
				parentheses --;
				if(parentheses == -1) {
					return i;
				}
			}
		}
		
		// do not find the first unbalance close parenthese
		return -1;
	}
}