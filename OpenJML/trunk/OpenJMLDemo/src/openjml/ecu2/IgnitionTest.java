public class IgnitionTest {

	//@ ensures true;
	public static void main(String[] args) {
		SensorValue rpmSensor = new SensorValue(1000, 0, 8000);
		IgnitionModule im = new IgnitionModule(rpmSensor);
		for(int r=2000; r<6000; r+=10) {
			rpmSensor.readSensor(r);
			int ign = im.getIgnition();
			System.out.printf("RPM: %04d, IGN: %03d\r", rpmSensor.getValue(), ign);
		}
	}
}
