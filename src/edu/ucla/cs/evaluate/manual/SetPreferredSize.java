package edu.ucla.cs.evaluate.manual;

import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.main.AnomalyDetection;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;

public class SetPreferredSize {
	public static void main(String[] args) {
		ArrayList<APISeqItem> pattern1 = new ArrayList<APISeqItem>();
		pattern1.add(new APICall("setPreferredSize", "true"));
		pattern1.add(new APICall("pack", "true"));
		
		HashSet<ArrayList<APISeqItem>> patterns = new HashSet<ArrayList<APISeqItem>>();
		patterns.add(pattern1);
		
		HashSet<String> types = new HashSet<String>();
		types.add("JFrame");
		HashSet<ArrayList<String>> queries = new HashSet<ArrayList<String>>();
		ArrayList<String> apis = new ArrayList<String>();
		apis.add("setPreferredSize");
		queries.add(apis);
		
		AnomalyDetection detect = new AnomalyDetection(types, queries, patterns);
		detect.run();
	}
}
