package edu.ucla.cs.mine;

import java.math.RoundingMode;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.utils.FileUtils;

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
				continue;
			}
			
			
			// Additional filter: remove empty control construct blocks unless it is an if check following an API call
			ArrayList<Integer> indices = new ArrayList<Integer>();
			for(int i = 0; i < pattern.size(); i ++) {
				String item = pattern.get(i);
				if(item.equals("IF {") || item.equals("TRY {") || item.equals("LOOP {") || item.equals("CATCH {") || item.equals("ELSE {") || item.equals("FINALLY {")) {
					if(i < pattern.size() - 1) {
						String next = pattern.get(i+1);
						if(next.equals("}")) {
							if(item.equals("IF {") && i > 0) {
								String prev = pattern.get(i-1);
								if(prev.contains("(")) {
									// value check
									continue;
								}
							}
							
							indices.add(i);
							indices.add(i+1);
						} else if (item.equals("CATCH {") && i > 0) {
							String prev = pattern.get(i-1);
							if(!prev.equals("}")) {
								remove.add(pattern);
							}
						}
					}
				} else if (item.contains("(")) {
					int count = 0;
					for(int j = 0; j < pattern.size(); j ++) {
						if(pattern.get(j).equals(item)) {
							count++;
						}
					}
					if(count > 1){
						// repetitive
						remove.add(pattern);
					}
				}
			}
			
			if(!indices.isEmpty()) {
				ArrayList<String> copy = new ArrayList<String>(pattern);
				for(int i = indices.size() - 1; i >= 0; i--) {
					Integer index = indices.get(i);
					copy.remove(index);
				}
				
				if(this.patterns.keySet().contains(copy)) {
					remove.add(pattern);
				}
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
		q1.add("read(0)");
		queries.add(q1);
		//query.add("mkdirs");
		// learn from the output of the light-weight output
		//PatternMiner pm = new FrequentSequenceMiner("/home/troy/research/BOA/Maple/mining/freq_seq.py", 
		//		"/home/troy/research/BOA/Maple/example/output.txt",
		//		40,
		//		query);
		
		// learn from the output of the traditional output
		SequencePatternMiner pm = new FrequentSequenceMiner("/home/troy/research/BOA/Maple/mining/freq_seq.py", 
				"/home/troy/research/BOA/Maple/example/InputStream.read/1/large-output.txt",
				(int) (21581 * 0.16),
				queries);

		pm.mine();
		for(ArrayList<String> pattern : pm.patterns.keySet()) {
			System.out.println(pattern + ":" + pm.patterns.get(pattern));
		}
	}
}
