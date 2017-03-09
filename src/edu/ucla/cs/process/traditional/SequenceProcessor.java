package edu.ucla.cs.process.traditional;

import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.ucla.cs.model.Method;

public class SequenceProcessor extends ProcessStrategy{
	static final Pattern METHOD_CALL = Pattern.compile("((new )?[a-zA-Z0-9_]+)\\(((.+),)*\\)");

	@Override
	void process(String line) {
		Method m = getMethodInstance(line);
		buildSequenceMap(m, line);
	}
	
	protected void buildSequenceMap(Method method, String line) {
		String s = line.substring(line.indexOf("] =") + 3).trim();
		String[] ss = s.split("->");
		// skip the first element because it is empty string
		for(int i = 1; i < ss.length; i++){
			if (ss[i].contains("}")){
				String str = ss[i].trim();
				while(str.contains("}")) {
					String sub1 = str.substring(0, str.indexOf("}")).trim();
					if(!sub1.isEmpty()) {
						method.seq.addAll(extractItems(sub1));
					}
					method.seq.add("}");
					str = str.substring(str.indexOf("}") + 1);
				}
				
				if(!str.isEmpty()) {
					method.seq.addAll(extractItems(str));
				}
			} else{
				method.seq.addAll(extractItems(ss[i].trim()));
			}
		}
	}
	
	public ArrayList<String> extractItems(String expr) {
		ArrayList<String> items = new ArrayList<String>();
		
		// check if it is a control-flow construct
		String s = expr.trim();
		if(s.equals("IF {") || s.equals("ELSE {") || s.equals("TRY {") || s.equals("CATCH {") || s.equals("LOOP {") || s.equals("FINALLY {")) {
			items.add(s);
			return items;
		}
		
		String[] ss = s.split("@");
		// we assume the last @ splits the statement and its precondition
		// but we will run into trouble if there is an @ in the precondition
		if(ss.length == 1) {
			s = ss[0];
		} else {
			s = ss[ss.length - 2];
		}
		
		
		// pre-check to avoid unnecessary pattern matching for the performance purpose
		if(s.contains("(") && s.contains(")")) {
			// extract method calls
			return extractMethodCalls(s);
		} else {
			// no method call, skip
			return items;
		}
	}
	
	private ArrayList<String> extractMethodCalls(String expr) {
		ArrayList<String> items = new ArrayList<String>();
		Matcher m = METHOD_CALL.matcher(expr);
		while(m.find()) {
			String apiName = m.group(1);
			String args = m.group(3);
			if(args != null) {
				// this api call has arguments
				ArrayList<String> apis2 = extractMethodCalls(args);
				items.addAll(apis2);
			}
			items.add(apiName);
		}
		
		return items;
	}
}
