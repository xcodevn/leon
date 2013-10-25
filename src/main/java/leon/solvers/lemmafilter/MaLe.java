package leon.solvers.lemmafilter.MaLe;
import java.util.ArrayList;
import java.util.concurrent.ConcurrentHashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.io.*;
import java.nio.file.Files;
import java.nio.charset.Charset;
import java.nio.file.Paths;
import java.lang.Math;

class Example {
	public List<String> features;
	public List<String> dependences;

	public Example(List<String> features, List<String> rules) {
		this.features = features;
		this.dependences = rules;
	}
}

class Classifier {
	private double bias;
	private ConcurrentHashMap<String, Double> wi;
	private String name;
	public String getName() { return name; }
	public Classifier(String name, Double bias, ConcurrentHashMap<String, Double> wi) { this.bias = bias;
		this.wi = wi;
		this.name = name;
	}
	public double P(List<String> lst) {
		double s = 0;
		for (String ft : lst) {
			if (this.wi.containsKey(ft))
				s += wi.get(ft);
		}

		return 1.0 / (1.0 + Math.exp(-s));
	}

	public String toString() {
		String s = "";
		for (Map.Entry<String, Double> entry : wi.entrySet()) {
			String key = entry.getKey();
			Double value = entry.getValue();
			s = s + String.format(" %s %1.5f",key, value);
		}
		return String.format("%s %f%s", this.name, this.bias, s);
	}
	static Classifier parse(String s) {
		Scanner sc = new Scanner(s).useDelimiter(" ");
		String name = sc.next();
		Double bias = sc.nextDouble();

		ConcurrentHashMap<String, Double> wi = new ConcurrentHashMap<String, Double> ();
		while (sc.hasNext()) {
			String rule = sc.next();
			Double vl = sc.nextDouble();
			wi.put(rule, vl);
		}
		return new Classifier(name, bias, wi);
	}
}

public class MaLe {

	ConcurrentHashMap<String,Classifier> map = new ConcurrentHashMap<String,Classifier> ();

	public MaLe() {
	}


	/* Load data file into memory */
	public void loadData(String fileName) {
		try {
			List<String> lst = Files.readAllLines(Paths.get(fileName), Charset.defaultCharset());
			for (String line : lst) {
				Classifier cf = Classifier.parse(line);
				map.put(cf.getName(), cf);
			}
		} catch (IOException e) {
			System.out.print("Exception");
		}
	}

	private double P(int c, int s) { 
		if (c == 0) return 1e-10;
		else return c * 1.0 / s ; 
	}

	public void writeOutFile(String fileName) {
		try {
			File file = new File(fileName);
			BufferedWriter output = new BufferedWriter(new FileWriter(file));
			for (Map.Entry<String, Classifier> entry : map.entrySet()) {
				String key = entry.getKey();
				Classifier cf = entry.getValue();
				output.write(cf.toString() + "\n");
			}
			output.close();
		} catch ( IOException e ) {
			e.printStackTrace();
		}


	}

	public void training(List<String> rules, List<String> features, List<Example> lstEg) {
		map.clear();
		for (String rule : rules) {
			ConcurrentHashMap<String, Integer> cFT = new ConcurrentHashMap<String, Integer> ();
			ConcurrentHashMap<String, Integer> cFF = new ConcurrentHashMap<String, Integer> ();
			ConcurrentHashMap<String, Double> wi = new ConcurrentHashMap<String, Double> ();
			/* Init our map */
			for (String ft : features) {
				cFT.put(ft, 0);
				cFF.put(ft, 0);
			}
			int c = 0;
			for (Example e : lstEg) {
				if (e.dependences.contains(rule)) {
					c ++;
					for (String f : e.features) {
						cFT.put(f, 1 + cFT.get(f));
					}
				} else {
					for (String f : e.features) {
						cFF.put(f, 1 + cFF.get(f));
					}
				}
			}
			int nc =  lstEg.size() - c;

			double bias = Math.log( P(c, lstEg.size()) / P(nc, lstEg.size()));
			// System.out.println(String.format("Rule %s", rule));
			for (String f:  features) { 
				// System.out.println(String.format("f: %s : cFT %d c %d CFF %d nc %d", f, cFT.get(f), c, cFF.get(f), nc));
				wi.put(f, Math.log(P(cFT.get(f),c) / P(cFF.get(f), nc)));
			}
			Classifier cf = new Classifier (rule, bias, wi );
			map.put(rule, cf);
		}
	}

	/* Return a value between 0 and 1.0 for probability value */
	public double classify(String ruleName, List<String> features) {
		Classifier cf = map.get(ruleName);
		return cf.P(features);
	}
}
