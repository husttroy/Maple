package edu.ucla.cs.utils;

import java.util.ArrayList;

public class ProcessUtils {
	public static ArrayList<String> splitByArrow(String s) {
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
	
	public static boolean isBalanced(String expr) {
		boolean inSingleQuote = false;
		boolean inDoubleQuote = false;
		int parentheses = 0;
		char[] chars = expr.toCharArray();
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
					// double quote ends
					inDoubleQuote = false;
				} else {
					// escape quote, not the end of the quote
				}
			} else if(cur == '"' && !inSingleQuote && !inDoubleQuote) {
				// double quote starts
				inDoubleQuote = true;
			} else if(cur == '\'' && !inSingleQuote && !inDoubleQuote) {
				// single quote starts
				inSingleQuote = true;
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
					// single quote ends
					inSingleQuote = false;
				} else {
					// escape single quote, not the end of the quote
				}
			} else if(cur == '"' && !inSingleQuote && inDoubleQuote) {
				// double quote ends
				inDoubleQuote = false;
			} else if (cur == '\'' && inSingleQuote && !inDoubleQuote) {
				// single quote ends
				inSingleQuote = false;
			} else if (inSingleQuote || inDoubleQuote) {
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
	
	public static int findFirstUnbalancedCloseParenthesis(String expr) {
		boolean inSingleQuote = false;
		boolean inDoubleQuote = false;
		int parentheses = 0;
		char[] chars = expr.toCharArray();
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
					// double quote ends
					inDoubleQuote = false;
				} else {
					// escape quote, not the end of the quote
				}
			} else if(cur == '"' && !inSingleQuote && !inDoubleQuote) {
				// double quote starts
				inDoubleQuote = true;
			} else if(cur == '\'' && !inSingleQuote && !inDoubleQuote) {
				// single quote starts
				inSingleQuote = true;
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
					// single quote ends
					inSingleQuote = false;
				} else {
					// escape single quote, not the end of the quote
				}
			} else if(cur == '"' && !inSingleQuote && inDoubleQuote) {
				// double quote ends
				inDoubleQuote = false;
			} else if (cur == '\'' && inSingleQuote && !inDoubleQuote) {
				// single quote ends
				inSingleQuote = false;
			} else if (inSingleQuote || inDoubleQuote) {
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
		
		// do not find the first unbalanced close parenthesis
		return -1;
	}

	public static boolean isInQuote(String s, int index) {
		if(s.contains("\"") || s.contains("'")) {
			char[] chars = s.toCharArray();
			boolean inSingleQuote = false;
			boolean inDoubleQuote = false;
			for(int i = 0; i < chars.length; i++) {
				if(i == index) {
					return inSingleQuote || inDoubleQuote;
				}
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
						// double quote ends
						inDoubleQuote = false;
					} else {
						// escape quote, not the end of the quote
					}
				} else if(cur == '"' && !inSingleQuote && !inDoubleQuote) {
					// double quote starts
					inDoubleQuote = true;
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
						// single quote ends
						inSingleQuote = false;
					} else {
						// escape single quote, not the end of the quote
					}
				} else if(cur == '\'' && !inSingleQuote && !inDoubleQuote) {
					// single quote starts
					inSingleQuote = true; 
				} else if(cur == '"' && !inSingleQuote && inDoubleQuote) {
					// double quote ends
					inDoubleQuote = false;
				} else if (cur == '\'' && inSingleQuote && !inDoubleQuote) {
					// single quote ends
					inSingleQuote = false;
				}
			}
			
			return inSingleQuote;
		} else {
			return false;
		}
	}
}
