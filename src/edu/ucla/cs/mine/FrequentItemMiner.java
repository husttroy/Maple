package edu.ucla.cs.mine;

import java.util.ArrayList;

public class FrequentItemMiner extends PatternMiner{

	public FrequentItemMiner(String script_path, String seqs_path,
			int min_support, ArrayList<String> query) {
		super(script_path, seqs_path, min_support, query);
	}

	@Override
	protected ArrayList<ArrayList<String>> process(String input) {
		ArrayList<ArrayList<String>> patterns = new ArrayList<ArrayList<String>>();
		String[] ss = input.split(System.lineSeparator());
		
		for(String s : ss) {
			// process each pattern detected by the frequent item miner
			if(s.contains("frozenset")) {
				ArrayList<String> pattern = new ArrayList<String>();
				s = s.substring(s.indexOf("[") + 1, s.lastIndexOf("]"));
				String[] arr = s.split(", ");
				for(String api : arr){
					// strip ' '
					api = api.substring(1, api.length()-1);
					pattern.add(api);
				}
				
				patterns.add(pattern);
			}
		}
		
		return patterns;
	}

	@Override
	protected void filter(ArrayList<ArrayList<String>> patterns,
			ArrayList<String> query) {
		ArrayList<ArrayList<String>> remove = new ArrayList<ArrayList<String>>();
		for(int i = 0; i < patterns.size(); i++) {
			ArrayList<String> pattern = patterns.get(i);
			if(!pattern.containsAll(query) || !isBalanced(pattern) || !isComplete(pattern)){
				remove.add(pattern);
			}
		}
		patterns.removeAll(remove);
	}
	
	public static void main(String[] args){
		ArrayList<String> query = new ArrayList<String>();
		query.add("createNewFile");
		PatternMiner pm = new FrequentItemMiner("/home/troy/research/BOA/Slicer/mining/freq_itemset.py", 
				"/home/troy/research/BOA/Slicer/example/output.txt",
				40,
				query);
		ArrayList<ArrayList<String>> patterns = pm.mine();
		for(ArrayList<String> pattern : patterns) {
			System.out.println(pattern);
		}
	}
}
