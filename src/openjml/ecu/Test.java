import java.util.Random;


public class Test {

	public static void main(String[] args) {
		Random r = new Random();
		r.setSeed(1234334543);
		SensorValue rpmSensor = new SensorValue(1000, 0, 8000);
		LookupScale rpmScale = new LookupScale(600, 8000, 16);
		LookupTable1d ignitionIdle = new LookupTable1d(rpmScale,
			new int[] { 12, 8, 6, 8, 10, 12, 14, 16, 18, 20, 22, 25, 30, 32, 34, 36	
		});
		for(int i=0; i<1000; i++) {
			rpmSensor.readSensor(r.nextInt(10000));
			int ign = ignitionIdle.getValue(rpmSensor);
			System.out.printf("RPM: %04d, IGN: %03d\n", rpmSensor.value, ign);
		}
	}
}
