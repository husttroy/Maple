package edu.ucla.cs.mine;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;

public class PatternUtils {
	
	public static HashMap<String, ArrayList<String>> readAPISequences(String path){
		HashMap<String, ArrayList<String>> seqs = new HashMap<String, ArrayList<String>>();
		
		try (BufferedReader br = new BufferedReader(new FileReader(new File(path)))){
			String line;
			while((line = br.readLine()) != null) {
				if(line.contains("---")){
					String id = line.split("---")[0];
					String s = line.split("---")[1];
					s = s.substring(1, s.length() - 1);
					ArrayList<String> seq = new ArrayList<String>();
					for(String api : s.split(",")){
						seq.add(api.trim());
					}
					seqs.put(id, seq);
				}
			}
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}	
		
		return seqs;
	}
	
	public static HashMap<String, ArrayList<String>> readOnlyOneSequenceFromEachProject(String path) {
		HashMap<String, ArrayList<String>> seqs = new HashMap<String, ArrayList<String>>();
		
		try (BufferedReader br = new BufferedReader(new FileReader(new File(path)))){
			String line;
			while((line = br.readLine()) != null) {
				if(line.contains("---")){
					String id = line.split("---")[0];
					String project = id.split("\\*\\*")[0];
					String s = line.split("---")[1];
					s = s.substring(1, s.length() - 1);
					ArrayList<String> seq = new ArrayList<String>();
					for(String api : s.split(",")){
						seq.add(api.trim());
					}
					if(!seqs.containsKey(project)) {
						seqs.put(project, seq);
					}
				}
			}
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}	
		
		return seqs;
	}
	
	public static ArrayList<String> extractSequenceWithoutGuard(ArrayList<APISeqItem> pattern) {
		ArrayList<String> patternS = new ArrayList<String>();
		
		for(APISeqItem item : pattern) {
			if (item instanceof APICall) {
				APICall call = (APICall)item;
				patternS.add(call.name);
			} else if (item instanceof ControlConstruct) {
				ControlConstruct construct = (ControlConstruct)item;
				if(construct == ControlConstruct.CATCH) {
					patternS.add("CATCH {");
				} else if (construct == ControlConstruct.ELSE) {
					patternS.add("ELSE {");
				} else if (construct == ControlConstruct.END_BLOCK) {
					patternS.add("}");
				} else if (construct == ControlConstruct.FINALLY) {
					patternS.add("FINALLY {");
				} else if (construct == ControlConstruct.IF) {
					patternS.add("IF {");
				} else if (construct == ControlConstruct.LOOP) {
					patternS.add("LOOP {");
				} else if (construct == ControlConstruct.TRY) {
					patternS.add("TRY {");
				}
			}
		}
		
		return patternS;
	}
}
