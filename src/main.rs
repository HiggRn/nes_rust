use bus::Bus;
use cartridge::Rom;
use rand::Rng;
use sdl2::event::Event;
use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::pixels::PixelFormatEnum;
use sdl2::EventPump;

mod bus;
mod cartridge;
mod cpu;
mod opcode;

use cpu::Cpu;
use cpu::Mem;

fn main() {
    // init sdl2
    let sdl_context = sdl2::init().unwrap();
    let video_subsystem = sdl_context.video().unwrap();
    let window = video_subsystem
        .window("Snake game", (32.0 * 10.0) as u32, (32.0 * 10.0) as u32)
        .position_centered()
        .build()
        .unwrap();

    let mut canvas = window.into_canvas().present_vsync().build().unwrap();
    let mut event_pump = sdl_context.event_pump().unwrap();
    canvas.set_scale(10.0, 10.0).unwrap();

    let creator = canvas.texture_creator();
    let mut texture = creator
        .create_texture_target(PixelFormatEnum::RGB24, 32, 32)
        .unwrap();

    // load the game
    let bytes = std::fs::read("snake.nes").unwrap();
    let rom = Rom::new(&bytes).unwrap();

    let bus = Bus::new(rom);
    let mut cpu = Cpu::new(bus);
    cpu.reset();

    let mut screen_state = [0u8; 32 * 3 * 32];
    let mut rng = rand::thread_rng();

    // run the game cycle
    cpu.run(move |cpu| {
        // read user input and write it to mem[0xFF]
        handle_user_input(cpu, &mut event_pump);

        // update mem[0xFE] with new random number
        cpu.mem_write(0xFE, rng.gen_range(1..16));

        // read mem mapped screen state
        if read_screen_state(cpu, &mut screen_state) {
            // render screen state
            texture.update(None, &screen_state, 32 * 3).unwrap();
            canvas.copy(&texture, None, None).unwrap();
            canvas.present();
        }

        std::thread::sleep(std::time::Duration::new(0, 1000));
    });
}

fn color(byte: u8) -> Color {
    match byte {
        0 => Color::BLACK,
        1 => Color::WHITE,
        2 | 9 => Color::GREY,
        3 | 10 => Color::RED,
        4 | 11 => Color::GREEN,
        5 | 12 => Color::BLUE,
        6 | 13 => Color::MAGENTA,
        7 | 14 => Color::YELLOW,
        _ => Color::CYAN,
    }
}

fn read_screen_state(cpu: &Cpu, frame: &mut [u8; 32 * 3 * 32]) -> bool {
    let mut frame_idx = 0;
    let mut update = false;
    for i in 0x0200..0x600 {
        let color_idx = cpu.mem_read(i as u16);
        let (b1, b2, b3) = color(color_idx).rgb();
        if frame[frame_idx] != b1 || frame[frame_idx + 1] != b2 || frame[frame_idx + 2] != b3 {
            frame[frame_idx] = b1;
            frame[frame_idx + 1] = b2;
            frame[frame_idx + 2] = b3;
            update = true;
        }
        frame_idx += 3;
    }
    update
}

fn handle_user_input(cpu: &mut Cpu, event_pump: &mut EventPump) {
    for event in event_pump.poll_iter() {
        match event {
            Event::Quit { .. }
            | Event::KeyDown {
                keycode: Some(Keycode::Escape),
                ..
            } => std::process::exit(0),
            Event::KeyDown {
                keycode: Some(Keycode::W),
                ..
            } => cpu.mem_write(0xFF, 0x77),
            Event::KeyDown {
                keycode: Some(Keycode::S),
                ..
            } => cpu.mem_write(0xFF, 0x73),
            Event::KeyDown {
                keycode: Some(Keycode::A),
                ..
            } => cpu.mem_write(0xFF, 0x61),
            Event::KeyDown {
                keycode: Some(Keycode::D),
                ..
            } => cpu.mem_write(0xFF, 0x64),
            _ => {} // do nothing
        }
    }
}
