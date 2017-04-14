package edu.ucla.cs.mine;

import java.util.ArrayList;
import java.util.HashSet;

public class FrequentSequenceMiner extends SequencePatternMiner {

	public FrequentSequenceMiner(String script_path, String seqs_path,
			int min_support, HashSet<HashSet<String>> filters) {
		super(script_path, seqs_path, min_support, filters);
	}

	@Override
	protected void process(String input) {
		String[] ss = input.split(System.lineSeparator());
		
		for(String s : ss) {
			// process each pattern detected by the frequent item miner
			if(s.startsWith("(") && s.endsWith(")")) {
				int support = Integer.valueOf(s.substring(s.lastIndexOf(", ") + 2, s.lastIndexOf(")")));
				String sequence = s.substring(s.indexOf("(") + 1, s.lastIndexOf(", "));
				
				ArrayList<String> pattern = new ArrayList<String>();
				sequence = sequence.substring(sequence.indexOf("(") + 1, sequence.lastIndexOf(")"));
				String[] arr = sequence.split(",");
				for(String api : arr){
					api = api.trim();
					// strip ' '
					api = api.substring(1, api.length()-1);
					pattern.add(api);
				}
				
				this.patterns.put(pattern, support);
			}
		}
	}

	@Override
	protected void filter() {
		ArrayList<ArrayList<String>> remove = new ArrayList<ArrayList<String>>();
		
		// check whether each pattern is satisfiable
		for(ArrayList<String> pattern : this.patterns.keySet()) {
			if(!isBalanced(pattern) || !isComplete(pattern)) {
				remove.add(pattern);
				continue;
			}
			
			boolean flag = false;
			for(HashSet<String> query : this.queries) {
				if(pattern.containsAll(query)){
					flag = true;
				}
			}
			
			if(!flag) {
				// does not follow any queries
				remove.add(pattern);
			}
		}
		
		// remove unsatisfied patterns
		for(ArrayList<String> pattern : remove) {
			this.patterns.remove(pattern);
		}
	}
	
	public static void main(String[] args){
		HashSet<HashSet<String>> queries = new HashSet<HashSet<String>>();
		HashSet<String> q1 = new HashSet<String>();
		q1.add("nextToken(0)");
		queries.add(q1);
		//query.add("mkdirs");
		// learn from the output of the light-weight output
		//PatternMiner pm = new FrequentSequenceMiner("/home/troy/research/BOA/Maple/mining/freq_seq.py", 
		//		"/home/troy/research/BOA/Maple/example/output.txt",
		//		40,
		//		query);
		
		// learn from the output of the traditional output
		SequencePatternMiner pm = new FrequentSequenceMiner("/home/troy/research/BOA/Maple/mining/freq_seq.py", 
				"/home/troy/research/BOA/Maple/example/StringTokenizer.nextToken/small-output.txt",
				50,
				queries);

		pm.mine();
		for(ArrayList<String> pattern : pm.patterns.keySet()) {
			System.out.println(pattern + ":" + pm.patterns.get(pattern));
		}
	}
}
