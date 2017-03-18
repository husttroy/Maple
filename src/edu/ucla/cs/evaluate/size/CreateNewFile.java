package edu.ucla.cs.evaluate.size;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.mine.FrequentSequenceMiner;
import edu.ucla.cs.mine.SequencePatternMiner;
import edu.ucla.cs.utils.FileUtils;

public class CreateNewFile {
	public static void main(String[] args) throws IOException {
		String path = "/home/troy/research/BOA/Maple/example/File.createNewFile/large-output.txt";
		HashSet<String> query = new HashSet<String>();
		query.add("createNewFile");
		Sample sam = new Sample(path);
		int[] sizes = {50, 100, 250, 500, 750, 1000, 2500, 5000, 7500, 10000};
		for(int i : sizes) {
			if(i <= sam.seqs.size()) {
				ArrayList<String> sample = sam.sample(i);
				String output = path.substring(0, path.lastIndexOf(".")) + "-sample-" + i + ".txt";
				File f = new File(output);
				if(!f.exists()) {
					f.createNewFile();
				}
				FileUtils.writeArrayToFile(sample, output);
				SequencePatternMiner pm = new FrequentSequenceMiner("/home/troy/research/BOA/Maple/mining/freq_seq.py", 
						output,
						(int) (0.5 * i),
						query);

				pm.mine();
				
				System.out.println("Size=" + (int) (0.5 * i));
				for(ArrayList<String> pattern : pm.patterns.keySet()) {
					System.out.println(pattern + ":" + pm.patterns.get(pattern));
				}
			}
		}
	}
}
