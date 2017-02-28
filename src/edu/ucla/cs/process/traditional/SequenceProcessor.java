package edu.ucla.cs.process.traditional;

import org.apache.commons.lang3.StringUtils;

import edu.ucla.cs.model.Method;

public class SequenceProcessor extends ProcessStrategy{

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
				String api = ss[i].split("}")[0];
				method.seq.add(normalizeAPICall(api));
				// count how many curly braces
				int n = StringUtils.countMatches(ss[i], '}');
				for(int j = 0; j < n; j++) {
					method.seq.add("}");
				}
			}else{
				method.seq.add(normalizeAPICall(ss[i].trim()));
			}
		}
	}
	
	
	/**
	 * 
	 * Normalize API call by (1) removing the receiver, 
	 * (2) removing arguments, (3) removing assignments, 
	 * (4) removing path conditions, (5) removing parentheses 
	 * 
	 * @param api
	 * @return
	 */
	private String normalizeAPICall(String api) {
		if(api.contains("=")) {
			api = api.split("=")[1];
		}
		
		if(api.contains("@")) {
			api = api.split("@")[0];
		}
		
		if(api.contains(".")) {
			String[] arr = api.split("\\.");
			api = arr[arr.length - 1];
		}
		
		if(api.contains("(")) {
			api = api.substring(0, api.indexOf("(")).trim();
		}
		
		return api;
	}
}
