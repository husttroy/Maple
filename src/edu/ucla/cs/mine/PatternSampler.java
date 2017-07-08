package edu.ucla.cs.mine;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.utils.SAT;

public class PatternSampler {
	public String seqFile;
	public String orgFile;
	public HashMap<String, ArrayList<String>> seqs;
	
	public PatternSampler(String seqFile, String orgFile) {
		this.seqFile = seqFile;
		this.orgFile = orgFile;
		seqs = PatternUtils.readAPISequences(seqFile);
	}
	
	public ArrayList<String> sample(ArrayList<APISeqItem> pattern, int n) {
		ArrayList<String> sample = new ArrayList<String>();
		
		// extract the API call sequence only without guard conditions
		ArrayList<String> patternS = PatternUtils.extractSequenceWithoutGuardAndArgCount(pattern);
		SequencePatternVerifier verifyS = new SequencePatternVerifier(patternS);
		verifyS.verify(seqFile);
		
		TraditionalPredicateMiner minerP = new TraditionalPredicateMiner(patternS, orgFile, seqFile);
		minerP.loadAndFilterPredicate();
		
		ArrayList<String> sampleIDs = new ArrayList<String>();
		SAT sat = new SAT();
		for(String id : verifyS.support.keySet()) {
			HashMap<String, ArrayList<String>> map = minerP.predicates.get(id);
			boolean flag = true;
			for(APISeqItem item : pattern) {
				if(!flag) {
					break;
				}
				if(item instanceof APICall) {
					APICall call = (APICall)item;
					if(call.condition.equals("true")) {
						continue;
					} else {
						ArrayList<String> predicates = map.get(call.name);
						for(String predicate : predicates) {
							if (!sat.checkImplication(predicate, call.condition)) {
								flag = false;
								break;
							}
						}
					}
				}
			}
			
			if(flag) {
				sampleIDs.add(id);
				if(sampleIDs.size() == n) {
					break;
				}
			}
		}
		
		// read the original file again to get the complete sequence of each sample 
		File output = new File(orgFile);
		try (BufferedReader br = new BufferedReader(new FileReader(output))) {
			String line;
			while ((line = br.readLine()) != null) {
				if(!line.startsWith("results[")) {
					continue;
				}
				String key = line.substring(line.indexOf("[") + 1,
						line.indexOf("][SEQ]"));
				key = key.replaceAll("\\!", " ** ");
				if(sampleIDs.contains(key)) {
					sample.add(line);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return sample;
	}
}
