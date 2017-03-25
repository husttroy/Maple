package edu.ucla.cs.evaluate.manual;

import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.main.AnomalyDetection;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;

public class Mkdirs {
	public static void main(String[] args) {
		ArrayList<APISeqItem> pattern1 = new ArrayList<APISeqItem>();
		pattern1.add(ControlConstruct.IF);
		pattern1.add(new APICall("mkdirs", "!rcv.exists()"));
		pattern1.add(ControlConstruct.END_BLOCK);
		
		ArrayList<APISeqItem> pattern2 = new ArrayList<APISeqItem>();
		pattern2.add(ControlConstruct.IF);
		pattern2.add(ControlConstruct.END_BLOCK);
		pattern2.add(new APICall("mkdirs", "!rcv.exists()"));
		
		ArrayList<APISeqItem> pattern3 = new ArrayList<APISeqItem>();
		pattern3.add(new APICall("mkdirs", "true"));
		pattern3.add(ControlConstruct.IF);
		pattern3.add(ControlConstruct.END_BLOCK);
		
		HashSet<ArrayList<APISeqItem>> patterns = new HashSet<ArrayList<APISeqItem>>();
		patterns.add(pattern1);
		patterns.add(pattern2);
		patterns.add(pattern3);
		
		HashSet<String> types = new HashSet<String>();
		HashSet<HashSet<String>> queries = new HashSet<HashSet<String>>();
		HashSet<String> q1 = new HashSet<String>();
		q1.add("mkdirs");
		queries.add(q1);
		HashSet<String> q2 = new HashSet<String>();
		q2.add("mkdir");
		queries.add(q2);
		
		AnomalyDetection detect = new AnomalyDetection(types, queries, patterns);
		detect.run();
	}
}
