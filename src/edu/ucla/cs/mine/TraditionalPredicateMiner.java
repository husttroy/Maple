package edu.ucla.cs.mine;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class TraditionalPredicateMiner extends PredicateMiner{
	
	final String path = "/home/troy/research/BOA/Maple/example/new_sequence.txt";
	final String sequence_path = "/home/troy/research/BOA/Maple/example/new_output.txt";
	
	public TraditionalPredicateMiner(ArrayList<String> pattern) {
		super(pattern);
	}

	@Override
	protected void loadAndFilterPredicate() {
		// find API call sequences that follow the pattern
		PatternVerifier pv = new PatternVerifier(pattern);
		pv.verify(sequence_path);
		
		// read the full output of the traditional analysis
		File output = new File(path);
		try (BufferedReader br = new BufferedReader(new FileReader(output))) {
			String line;
			while ((line = br.readLine()) != null) {
				String key = line.substring(line.indexOf("[") + 1, line.indexOf("]"));
				key = key.replaceAll("\\!", " ** ");
				if(pv.support.containsKey(key)) {
					// this sequence follows the pattern
					String seq = line.substring(line.indexOf("] =") + 3).trim();
					String[] arr = seq.split("->");
					
					HashMap<String, ArrayList<String>> map = new HashMap<String, ArrayList<String>>();
					// skip the first element because it is empty string
					for(int i = 1; i < arr.length; i++){
						String api;
						if (arr[i].contains("}")){
							api = arr[i].split("}")[0];
							
						}else{
							api = arr[i];
						}
						
						String name = getAPICallName(api);
						if(!pattern.contains(name)) {
							continue;
						}
						
						String predicate = getPredicate(api);
						
						if(predicate.isEmpty()) {
							predicate = "true";
						} else {
							String receiver = getReceiver(api);
							ArrayList<String> args = getArguments(api);
							
							HashSet<String> relevant_elements = new HashSet<String>();
							relevant_elements.add(receiver);
							relevant_elements.addAll(args);
							
							// remove irrelevant clauses
							predicate = condition(relevant_elements, predicate);
							
							// normalize names
							// declare temporary variables to fit the API
							ArrayList<String> temp1 = new ArrayList<String>();
							temp1.add(receiver);
							ArrayList<ArrayList<String>> temp2 = new ArrayList<ArrayList<String>>();
							temp2.add(args);
							
							predicate = normalize(predicate, temp1, temp2);
						}
						
						ArrayList<String> ps;
						if(map.containsKey(name)){
							ps = map.get(name);
						} else {
							ps = new ArrayList<String>();
						}
						
						ps.add(predicate);
						map.put(name, ps);
					}
					
					this.predicates.put(key, map);
				}
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
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
	private String getAPICallName(String api) {
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
		
		return api.trim();
	}
	
	private String getReceiver(String api) {
		String rcv = null;
		if(api.contains("=")) {
			api = api.split("=")[1];
		}
		
		if(api.contains(".")) {
			String[] arr = api.split("\\.");
			rcv = arr[0];
		}
		
		return rcv.trim();
	}
	
	private ArrayList<String> getArguments(String api) {
		ArrayList<String> args = new ArrayList<String>();
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
			String temp = api.substring(api.indexOf("(") + 1, api.indexOf(")")).trim();
			if(temp.contains(",")) {
				String[] ss = temp.split(",");
				for(String s : ss) {
					if(!s.isEmpty()){
						args.add(s.trim());
					}
				}
			} else {
				if(!temp.isEmpty()) {
					args.add(temp);
				}
			}
		}
		
		return args;
	}
	
	private String getPredicate(String api) {
		String predicate = "";
		if(api.contains("=")) {
			api = api.split("=")[1];
		}
		
		if(api.contains("@") && !api.endsWith("@")) {
			predicate = api.split("@")[1];
		}
		
		return predicate.trim();
	}
	
	public static void main(String[] args) {
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("IF {");
		pattern.add("createNewFile");
		pattern.add("}");
		TraditionalPredicateMiner pm = new TraditionalPredicateMiner(pattern);
		pm.process();
	}
}
