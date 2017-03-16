package edu.ucla.cs.utils;

public class ProcessUtils {

	public static boolean isBalanced(String expr) {
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
	
	public static int findFirstUnbalancedCloseParenthesis(String expr) {
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
