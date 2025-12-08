import React, { useState, useRef, useEffect, useCallback, useMemo } from 'react';
import { Upload, Move, RefreshCw, ChevronUp, ChevronDown, ChevronLeft, ChevronRight, Ruler, ArrowLeft, ArrowRight, Loader2, Minus, Plus, Maximize2, Minimize2 } from 'lucide-react';

// 固定的基本寬度
const BASE_TARGET_WIDTH = 1000; 

const MAGNIFIER_SIZE = 225; 

// --- 輔助函數: 圖片載入 ---
const loadImage = (src) => {
    return new Promise((resolve, reject) => {
        const img = new Image();
        img.crossOrigin = "anonymous"; 
        img.onload = () => resolve(img);
        img.onerror = (e) => reject(new Error("圖片載入失敗，請確認檔案格式是否正確。"));
        img.src = src;
    });
};

// --- 核心函數: 矩陣運算工具 (Matrix Utility) ---
const Matrix = {
    // 矩陣乘法 (A * B)
    multiply: (A, B) => {
        const rowsA = A.length, colsA = A[0].length;
        const rowsB = B.length, colsB = B[0].length;

        if (colsA !== rowsB) throw new Error("矩陣尺寸不匹配");
        
        const C = Array(rowsA).fill(0).map(() => Array(colsB).fill(0));
        
        for (let i = 0; i < rowsA; i++) {
            for (let j = 0; j < colsB; j++) {
                let sum = 0;
                for (let k = 0; k < colsA; k++) {
                    sum += A[i][k] * B[k][j];
                }
                C[i][j] = sum;
            }
        }
        return C;
    },

    // 矩陣求逆
    inverse3x3: (M) => {
        const [a, b, c, d, e, f, g, h, i] = [
            M[0][0], M[0][1], M[0][2],
            M[1][0], M[1][1], M[1][2],
            M[2][0], M[2][1], M[2][2]
        ];

        const det = a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g);
        if (Math.abs(det) < 1e-6) return null;
        const invDet = 1 / det;

        return [
            [(e * i - f * h) * invDet, (c * h - b * i) * invDet, (b * f - c * e) * invDet],
            [(f * g - d * i) * invDet, (a * i - c * g) * invDet, (c * d - a * f) * invDet],
            [(d * h - e * g - 0) * invDet, (b * g - a * h) * invDet, (a * e - b * d) * invDet]
        ];
    },
    
    // 求解 Ax=B 的線性系統
    solveLinearSystem: (A, B) => {
        const n = A.length;
        const M = A.map((row, i) => [...row, B[i]]);

        for (let k = 0; k < n; k++) {
            let i_max = k;
            let v_max = M[k][k];
            for (let i = k + 1; i < n; i++) {
                if (Math.abs(M[i][k]) > Math.abs(v_max)) {
                    v_max = M[i][k];
                    i_max = i;
                }
            }
            if (M[i_max][k] === 0) throw new Error("線性系統奇異");
            
            [M[k], M[i_max]] = [M[i_max], M[k]];

            for (let i = k + 1; i < n; i++) {
                const f = M[i][k] / M[k][k];
                for (let j = k; j < n + 1; j++) {
                    M[i][j] = M[i][j] - M[k][j] * f;
                }
            }
        }

        const X = Array(n).fill(0); 
        for (let i = n - 1; i >= 0; i--) {
            let sum = 0;
            for (let j = i + 1; j < n; j++) sum += M[i][j] * X[j];
            X[i] = (M[i][n] - sum) / M[i][i]; 
        }
        return X;
    }
};

// --- 核心函數: 雙線性插值 ---
const bilinearInterpolation = (imageData, x, y) => {
    const { width, height, data } = imageData;
    const x1 = Math.floor(x), y1 = Math.floor(y);
    const x2 = Math.ceil(x), y2 = Math.ceil(y);

    if (x1 < 0 || x2 >= width || y1 < 0 || y2 >= height) return [0, 0, 0, 255]; 

    const fx = x - x1, fy = y - y1;
    const fx1 = 1 - fx, fy1 = 1 - fy;

    const getPixelIndex = (px, py) => (py * width + px) * 4;
    let r = 0, g = 0, b = 0, a = 0;
    
    // Helper for interpolation
    const interpolate = (idx, w) => {
        r += data[idx] * w; g += data[idx + 1] * w; b += data[idx + 2] * w; a += data[idx + 3] * w;
    }
    
    interpolate(getPixelIndex(x1, y1), fx1 * fy1);
    interpolate(getPixelIndex(x2, y1), fx * fy1);
    interpolate(getPixelIndex(x1, y2), fx1 * fy);
    interpolate(getPixelIndex(x2, y2), fx * fy);

    return [Math.round(r), Math.round(g), Math.round(b), Math.round(a)];
};

// --- 放大鏡組件 (Magnifier Component) ---
const Magnifier = React.memo(({ magnifierState, zoom, cardImage }) => { 
    const { visible, targetX, targetY, imgRect, currentStep, cropPoints, measureLines } = magnifierState;
    const canvasRef = useRef(null);
    const size = MAGNIFIER_SIZE; 
    const halfSize = size / 2;

    useEffect(() => {
        if (!visible || !canvasRef.current || !cardImage || !imgRect || imgRect.width === 0) return;

        const canvas = canvasRef.current;
        const ctx = canvas.getContext('2d');
        
        canvas.width = size;
        canvas.height = size;
        
        const img = cardImage;
        if (!img.complete) return; 

        // 1. 繪製放大後的圖像
        const normX = (targetX - imgRect.left);
        const normY = (targetY - imgRect.top);
        
        const imgW = img.naturalWidth;
        const imgH = img.naturalHeight;
        
        const imgRenderW = imgRect.width;
        const imgRenderH = imgRect.height;
        
        const norm_x_01 = normX / imgRenderW;
        const norm_y_01 = normY / imgRenderH;
        
        const srcX = norm_x_01 * imgW;
        const srcY = norm_y_01 * imgH;
        
        const clipW_px = size / zoom; 
        const clipH_px = size / zoom; 
        
        ctx.clearRect(0, 0, size, size);
        try {
            // 繪製裁切區域
            ctx.drawImage(img, srcX - clipW_px / 2, srcY - clipH_px / 2, clipW_px, clipH_px, 0, 0, size, size);
        } catch (e) {
            console.error("Magnifier drawImage failed:", e);
        }
        
        // 2. 繪製線條與點位
        const scale = size / clipW_px; 
        const offsetX = (srcX * scale) - halfSize;
        const offsetY = (srcY * scale) - halfSize;
        
        ctx.lineWidth = 2;
        // 設置虛線樣式 (用於測量和裁切線)
        ctx.setLineDash([5, 5]); 

        const drawNormalizedPoint = (norm_x, norm_y) => ({
            x: (norm_x * imgW * scale) - offsetX,
            y: (norm_y * imgH * scale) - offsetY,
        });

        if (currentStep === 'crop' && cropPoints && cropPoints.length === 4) {
            // 裁切框 (綠色虛線)
            ctx.strokeStyle = 'rgba(34, 197, 94, 1)'; 
            ctx.beginPath();
            const startPt = drawNormalizedPoint(cropPoints[0].x, cropPoints[0].y);
            ctx.moveTo(startPt.x, startPt.y);
            cropPoints.forEach((p, i) => {
                const pt = drawNormalizedPoint(p.x, p.y);
                if (i > 0) ctx.lineTo(pt.x, pt.y);
            });
            ctx.lineTo(startPt.x, startPt.y);
            ctx.stroke();

            // 裁切點 (綠色實心圓)
            ctx.setLineDash([]); // 圓形不需要虛線
            cropPoints.forEach((p) => {
                const pt = drawNormalizedPoint(p.x, p.y);
                ctx.fillStyle = 'rgba(34, 197, 94, 1)'; 
                ctx.beginPath();
                ctx.arc(pt.x, pt.y, 4 / Math.sqrt(zoom), 0, Math.PI * 2); 
                ctx.fill();
            });
            ctx.setLineDash([5, 5]); // 恢復虛線模式
        } else if (currentStep === 'measure' && measureLines) {
            // 測量線 (藍色/紅色虛線)
            const lines = measureLines;
            const drawLine = (val, isH, color) => {
                ctx.strokeStyle = color;
                ctx.beginPath();
                if (isH) {
                    const y = ((val / 100) * imgH * scale) - offsetY;
                    ctx.moveTo(0, y); ctx.lineTo(size, y);
                } else {
                    const x = ((val / 100) * imgW * scale) - offsetX;
                    ctx.moveTo(x, 0); ctx.lineTo(x, size);
                }
                ctx.stroke();
            };

            // 藍線 (卡邊)
            drawLine(lines.outerTop, true, 'rgba(59, 130, 246, 1)');
            drawLine(lines.outerBottom, true, 'rgba(59, 130, 246, 1)');
            drawLine(lines.outerLeft, false, 'rgba(59, 130, 246, 1)');
            drawLine(lines.outerRight, false, 'rgba(59, 130, 246, 1)');
            
            // 紅線 (圖案邊界)
            drawLine(lines.innerTop, true, 'rgba(239, 68, 68, 1)');
            drawLine(lines.innerBottom, true, 'rgba(239, 68, 68, 1)');
            drawLine(lines.innerLeft, false, 'rgba(239, 68, 68, 1)');
            drawLine(lines.innerRight, false, 'rgba(239, 68, 68, 1)');
        }
        
        // 3. 繪製中心紅點 (實心圓)
        ctx.setLineDash([]); 
        ctx.fillStyle = 'rgba(255, 0, 0, 0.8)';
        ctx.beginPath();
        ctx.arc(halfSize, halfSize, 3, 0, Math.PI * 2);
        ctx.fill();

    }, [visible, targetX, targetY, imgRect, cardImage, size, zoom, currentStep, cropPoints, measureLines]);

    if (!visible || !imgRect || imgRect.width === 0) return null;

    const finalLeft = targetX - halfSize;
    const finalTop = targetY - halfSize;

    const style = {
        left: `${finalLeft}px`, top: `${finalTop}px`, width: `${size}px`, height: `${size}px`,
    };

    return (
        // 放大鏡使用 fixed 定位是正確的，因為它跟隨滑鼠/觸控位置
        <div className="fixed rounded-full shadow-2xl z-[100] border-4 border-yellow-400 backdrop-blur-sm transition-opacity duration-150 overflow-hidden bg-gray-900/50" style={style}>
            <canvas ref={canvasRef} className="rounded-full w-full h-full"></canvas>
        </div>
    );
});


function CardGraderTool() {
  const [step, setStep] = useState('upload'); 
  const [originalImage, setOriginalImage] = useState(null); 
  const [processedImage, setProcessedImage] = useState(null); 
  const [isProcessing, setIsProcessing] = useState(false);
  const [zoomLevel, setZoomLevel] = useState(1.0); 
  
  // 新增: 控制放大鏡面板收折狀態
  const [isMagnifierPanelCollapsed, setIsMagnifierPanelCollapsed] = useState(false);

  const [originalCardDims, setOriginalCardDims] = useState({ w: 0, h: 0 }); 
  const [cropPoints, setCropPoints] = useState([]); 
  const [activePointIndex, setActivePointIndex] = useState(null); 

  const [measureLines, setMeasureLines] = useState({
    outerTop: 2, innerTop: 12, outerBottom: 98, innerBottom: 88,
    outerLeft: 3, innerLeft: 13, outerRight: 97, innerRight: 87
  });
  
  const measureLinesRef = useRef(measureLines);
  useEffect(() => { measureLinesRef.current = measureLines; }, [measureLines]);

  const [selectedLineId, setSelectedLineId] = useState(null); 
  const [draggingLineId, setDraggingLineId] = useState(null); 
  const [lastInteractionCoords, setLastInteractionCoords] = useState({});
  const currentMousePosRef = useRef({ clientX: 0, clientY: 0 });

  const [magnifier, setMagnifier] = useState({ 
      visible: false, targetX: 0, targetY: 0, imgRect: null, 
      currentStep: 'upload', cropPoints: [], measureLines: {}, isTrackingMouse: false
  }); 

  const containerRef = useRef(null);
  const imgRef = useRef(null);
  const magnifierTimeoutRef = useRef(null); 

  const cardImageForMagnifier = useMemo(() => {
    if (step === 'crop' && originalImage) return originalImage; 
    if (step === 'measure' && processedImage) return processedImage;
    return null;
  }, [step, originalImage, processedImage]);

  const zoomOptions = [0.2, 0.5, 1.0, 1.5, 2, 3, 5];

  // --- Helper: Get Live Image Rect (Crucial for scrolling/coordinate stability) ---
  const getLiveImageRect = useCallback(() => {
    if (!imgRef.current) return null;
    return imgRef.current.getBoundingClientRect();
  }, []);

  // --- Helper: Get Live Container Rect ---
  const getLiveContainerRect = useCallback(() => {
    if (!containerRef.current) return null;
    return containerRef.current.getBoundingClientRect();
  }, []);

  // --- Helper: Show Fixed Magnifier ---
  const showFixedMagnifierAt = useCallback((clientX, clientY) => {
    const imgRect = getLiveImageRect(); // 使用即時 Rect
    if (!imgRect || imgRect.width === 0) return;

    if (magnifierTimeoutRef.current) {
        clearTimeout(magnifierTimeoutRef.current);
        magnifierTimeoutRef.current = null;
    }
    
    setMagnifier(prev => ({
        ...prev, visible: true, isTrackingMouse: false, 
        targetX: clientX, targetY: clientY, imgRect: imgRect,
        currentStep: step, cropPoints: cropPoints, measureLines: measureLinesRef.current, 
    }));

    magnifierTimeoutRef.current = setTimeout(() => {
        setMagnifier(prev => ({ ...prev, visible: false, isTrackingMouse: false }));
        magnifierTimeoutRef.current = null;
    }, 2000); 
  }, [step, cropPoints, measureLinesRef, getLiveImageRect]); 

  // --- Helper: Get Screen Coordinates ---
  const getLineScreenCenter = useCallback((lineId) => {
    if (!lineId || !processedImage) return null;
    const imgRect = getLiveImageRect(); // 使用即時 Rect
    if (!imgRect || imgRect.width === 0) return null;

    const storedCoords = lastInteractionCoords[lineId];
    if (storedCoords) return storedCoords;

    const isH = lineId.includes('Top') || lineId.includes('Bottom');
    const lineVal = measureLinesRef.current[lineId] / 100; 

    let screenX, screenY;
    if (isH) {
        screenX = imgRect.left + imgRect.width / 2;
        screenY = imgRect.top + imgRect.height * lineVal;
    } else {
        screenX = imgRect.left + imgRect.width * lineVal;
        screenY = imgRect.top + imgRect.height / 2;
    }
    return { x: screenX, y: screenY };
  }, [processedImage, lastInteractionCoords, measureLinesRef, getLiveImageRect]);

  // --- Handlers: Upload ---
  const handleImageUpload = (e) => {
    const file = e.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = (event) => {
      const img = new Image();
      img.crossOrigin = "anonymous";
      img.onload = () => {
        setOriginalImage(img);
        const dims = { w: img.naturalWidth, h: img.naturalHeight };
        setOriginalCardDims(dims); 
        
        // 初始綠點位置 (Normalized)
        const initialCropPoints = [
          { x: 0.15, y: 0.15 }, { x: 0.85, y: 0.15 }, 
          { x: 0.85, y: 0.85 }, { x: 0.15, y: 0.85 }, 
        ];
        
        setCropPoints(initialCropPoints);
        setProcessedImage(null); 
        setStep('crop');
      };
      img.src = event.target.result;
    };
    reader.readAsDataURL(file);
  };

  // --- Helper: Coordinate Mapping ---
  const getScreenCoords = useCallback((normX, normY) => {
    const imgRect = getLiveImageRect(); // 使用即時 Rect
    if (!imgRect || imgRect.width === 0) return { x: -100, y: -100 };

    return {
      x: normX * imgRect.width + imgRect.left,
      y: normY * imgRect.height + imgRect.top,
      renderW: imgRect.width, renderH: imgRect.height, 
      offsetX: imgRect.left, offsetY: imgRect.top 
    };
  }, [getLiveImageRect]);

  const handleCropDragStart = (index, e) => {
    e.preventDefault(); e.stopPropagation(); 
    setActivePointIndex(index); setSelectedLineId(null); 
    if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
  };

  const handleLineDragStart = (id, e) => {
    e.stopPropagation(); 
    setSelectedLineId(id); setDraggingLineId(id); setActivePointIndex(null); 

    const clientX = e.touches ? e.touches[0].clientX : e.clientX;
    const clientY = e.touches ? e.touches[0].clientY : e.clientY;
    
    showFixedMagnifierAt(clientX, clientY);
    setLastInteractionCoords(prev => ({ ...prev, [id]: { x: clientX, y: clientY } }));
  };

  // Shared move handler
  const handleGlobalMove = useCallback((e) => {
    if (!containerRef.current) return;
    const clientX = e.touches ? e.touches[0].clientX : e.clientX;
    const clientY = e.touches ? e.touches[0].clientY : e.clientY;
    currentMousePosRef.current = { clientX, clientY };

    // *** 關鍵: 直接從 DOM 讀取圖片的即時位置 Rect ***
    const imgRect = getLiveImageRect(); 
    if (!imgRect || imgRect.width === 0) return; 

    const relativeX = clientX - imgRect.left;
    const relativeY = clientY - imgRect.top;

    let normX = Math.max(0, Math.min(1, relativeX / imgRect.width));
    let normY = Math.max(0, Math.min(1, relativeY / imgRect.height));

    if (step === 'crop' && activePointIndex !== null) {
      if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
      const nextCropPoints = [...cropPoints];
      nextCropPoints[activePointIndex] = { x: normX, y: normY };
      setCropPoints(nextCropPoints);
      
       setMagnifier(prev => ({ 
            ...prev, visible: true, isTrackingMouse: true, 
            targetX: clientX, targetY: clientY, imgRect: imgRect,
            currentStep: step, cropPoints: nextCropPoints, 
        }));

    } else if (step === 'measure' && draggingLineId) { 
       if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
       
       const valPct = (draggingLineId.includes('Left') || draggingLineId.includes('Right')) 
          ? normX * 100 : normY * 100;
       
       setMeasureLines(prev => ({ ...prev, [draggingLineId]: valPct }));
       
       setMagnifier(prev => ({ 
            ...prev, visible: true, isTrackingMouse: true, 
            targetX: clientX, targetY: clientY, imgRect: imgRect,
            measureLines: measureLinesRef.current, currentStep: step,
        }));
        setLastInteractionCoords(prev => ({ ...prev, [draggingLineId]: { x: clientX, y: clientY } }));
    } 
  }, [step, activePointIndex, draggingLineId, cropPoints, getLiveImageRect, showFixedMagnifierAt]); 

  const handleGlobalUp = useCallback(() => {
    const wasCropDragging = activePointIndex !== null;
    const wasLineDragging = draggingLineId !== null;
    setActivePointIndex(null); setDraggingLineId(null); 
    
    if (wasCropDragging || wasLineDragging) {
          setMagnifier(prev => ({ ...prev, visible: false, isTrackingMouse: false }));
          if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
    }
  }, [draggingLineId, activePointIndex]); 

  useEffect(() => {
    window.addEventListener('mousemove', handleGlobalMove);
    window.addEventListener('mouseup', handleGlobalUp);
    window.addEventListener('touchmove', handleGlobalTouchMove, { passive: false });
    window.addEventListener('touchend', handleGlobalUp);
    return () => {
      window.removeEventListener('mousemove', handleGlobalMove);
      window.removeEventListener('mouseup', handleGlobalUp);
      window.removeEventListener('touchmove', handleGlobalTouchMove);
      window.removeEventListener('touchend', handleGlobalUp);
    };
  }, [handleGlobalMove, handleGlobalUp]);

  const handleGlobalTouchMove = (e) => {
     if(activePointIndex !== null || draggingLineId !== null) {
         e.preventDefault(); handleGlobalMove(e);
     }
  };

  const performWarpAndProceed = useCallback(async () => {
    if (!originalImage || !originalImage.src) return; 
    setIsProcessing(true);
    try {
        const srcW = originalCardDims.w;
        const srcH = originalCardDims.h;

        // 移除強制 PTCG 比例的邏輯，永遠使用動態比例計算
        const P0 = cropPoints[0], P1 = cropPoints[1], P2 = cropPoints[2], P3 = cropPoints[3];
        // 使用實際像素計算距離
        const dist = (pA, pB) => Math.sqrt(Math.pow((pA.x - pB.x) * srcW, 2) + Math.pow((pA.y - pB.y) * srcH, 2));
        
        const avgW = (dist(P0, P1) + dist(P3, P2)) / 2;
        const avgH = (dist(P0, P3) + dist(P1, P2)) / 2;
        
        if (avgH < 1 || avgW < 1) throw new Error("裁剪區域無效。");
        
        const targetW = BASE_TARGET_WIDTH;
        const targetH = Math.max(100, Math.min(10000, Math.round(BASE_TARGET_WIDTH / (avgW / avgH)))); 
        
        const srcPoints = cropPoints.map(p => ([p.x * srcW, p.y * srcH]));
        const dstPoints = [[0, 0], [targetW, 0], [targetW, targetH], [0, targetH]];

        const A = [], B = [];
        for (let i = 0; i < 4; i++) {
            const [x, y] = srcPoints[i], [u, v] = dstPoints[i];
            A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); B.push(u); 
            A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); B.push(v);
        }
        const solution = Matrix.solveLinearSystem(A, B);
        const H_inv = Matrix.inverse3x3(
            [ (solution.slice(0,3)), (solution.slice(3,6)), (solution.slice(6,8).concat([1])) ].flat().reduce((acc, val, i) => {
                if(i % 3 === 0) acc.push([]);
                acc[acc.length-1].push(val);
                return acc;
            }, [])
        );

        if (!H_inv) throw new Error("矩陣奇異");

        const canvas = document.createElement('canvas');
        canvas.width = targetW; canvas.height = targetH;
        const ctx = canvas.getContext('2d');
        const tempImageForCanvas = await loadImage(originalImage.src);
        const tempCanvas = document.createElement('canvas');
        tempCanvas.width = srcW; tempCanvas.height = srcH;
        const tempCtx = tempCanvas.getContext('2d');
        tempCtx.drawImage(tempImageForCanvas, 0, 0, srcW, srcH);
        
        const srcImageData = tempCtx.getImageData(0, 0, srcW, srcH);
        const dstImageData = ctx.createImageData(targetW, targetH);
        const dstData = dstImageData.data;

        for (let y = 0; y < targetH; y++) {
            for (let x = 0; x < targetW; x++) {
                const target_vector = [[x], [y], [1]];
                const source_homogenous = Matrix.multiply(H_inv, target_vector);
                const wW = source_homogenous[2][0]; 
                const sourceX = source_homogenous[0][0] / wW;
                const sourceY = source_homogenous[1][0] / wW;
                const dstIdx = (y * targetW + x) * 4;
                
                if (sourceX >= 0 && sourceX < srcW - 1 && sourceY >= 0 && sourceY < srcH - 1) {
                    const [r, g, b, a] = bilinearInterpolation(srcImageData, sourceX, sourceY);
                    dstData[dstIdx] = r; dstData[dstIdx + 1] = g; dstData[dstIdx + 2] = b; dstData[dstIdx + 3] = a;
                } else {
                    dstData[dstIdx] = 0; dstData[dstIdx + 1] = 0; dstData[dstIdx + 2] = 0; dstData[dstIdx + 3] = 255;
                }
            }
        }
        
        ctx.putImageData(dstImageData, 0, 0);
        const newImg = new Image();
        newImg.onload = () => {
            setProcessedImage(newImg); setIsProcessing(false); setStep('measure');
            setSelectedLineId(null); setLastInteractionCoords({});
            if (containerRef.current) containerRef.current.scrollTop = 0;
        };
        newImg.src = canvas.toDataURL('image/png'); 
    } catch (error) {
        console.error("Homography error:", error);
        setIsProcessing(false);
    }
  }, [originalImage, originalCardDims, cropPoints]); 

  const calculateResults = () => {
    const topBorder = Math.abs(measureLines.innerTop - measureLines.outerTop);
    const bottomBorder = Math.abs(measureLines.outerBottom - measureLines.innerBottom);
    const leftBorder = Math.abs(measureLines.innerLeft - measureLines.outerLeft);
    const rightBorder = Math.abs(measureLines.outerRight - measureLines.innerRight);
    const totalV = topBorder + bottomBorder || 1;
    const totalH = leftBorder + rightBorder || 1;
    return {
        v: { top: (topBorder / totalV) * 100, bottom: (bottomBorder / totalV) * 100 },
        h: { left: (leftBorder / totalH) * 100, right: (rightBorder / totalH) * 100 }
    };
  };
  const results = calculateResults();

  const nudgeLine = (val) => {
    if (!selectedLineId || !processedImage) return;
    const lineIdToNudge = selectedLineId;
    const screenCenter = getLineScreenCenter(lineIdToNudge); 
    if (!screenCenter) return;
    
    const isHLine = lineIdToNudge.includes('Top') || lineIdToNudge.includes('Bottom');
    const imgRect = getLiveImageRect(); // Use live rect for nudge calc
    if(!imgRect) return;

    const pixelSize = isHLine ? imgRect.height : imgRect.width; 
    const pxPct = (1 / pixelSize) * 100;
    
    setMeasureLines(prev => ({
        ...prev,
        [lineIdToNudge]: Math.max(0, Math.min(100, prev[lineIdToNudge] + (val * pxPct)))
    }));
    
    showFixedMagnifierAt(screenCenter.x, screenCenter.y); 
  };
  
  const handleZoomChange = (newZoom) => {
      setZoomLevel(newZoom);
      let targetX, targetY;
      if (step === 'measure' && selectedLineId) {
          const screenCenter = getLineScreenCenter(selectedLineId);
          if (screenCenter) { targetX = screenCenter.x; targetY = screenCenter.y; }
      } else {
          const imgRect = getLiveImageRect();
          if (imgRect) { targetX = imgRect.left + imgRect.width / 2; targetY = imgRect.top + imgRect.height / 2; }
      }
      if (targetX !== undefined) showFixedMagnifierAt(targetX, targetY);
  }

  // Define renderDraggableLine INSIDE the component
  const renderDraggableLine = (id, orientation, colorClass, isInner) => {
    const val = measureLines[id];
    const isActive = selectedLineId === id; 
    const isHorizontal = orientation === 'horizontal';
    const style = isHorizontal ? { top: `${val}%` } : { left: `${val}%` };
    const cursor = isHorizontal ? 'cursor-row-resize' : 'cursor-col-resize';
    const hitAreaStyle = isHorizontal ? { top: '-10px', bottom: '-10px', left: 0, right: 0 } : { left: '-10px', right: '-10px', top: 0, bottom: 0 };
    const lineClasses = `absolute w-full h-full border border-dashed transition-colors ${isHorizontal ? 'border-t' : 'border-l'}`;

    return (
        <div key={id} className={`absolute z-20 group ${cursor}`} style={{...style, ...(isHorizontal ? {left:0, right:0, height:0} : {top:0, bottom:0, width:0})}}
            onMouseDown={(e) => handleLineDragStart(id, e)} onTouchStart={(e) => handleLineDragStart(id, e)}>
            <div className={`${lineClasses} ${isActive ? 'border-yellow-400 z-50 shadow-[0_0_5px_rgba(255,255,0,0.8)]' : colorClass}`}></div>
            <div className="absolute bg-transparent" style={hitAreaStyle}></div>
            {isActive && <div className={`absolute ${isHorizontal ? 'left-1/2 -top-6 transform -translate-x-1/2' : 'top-1/2 -left-6 transform -translate-y-1/2'} bg-gray-900 text-[10px] text-white px-1 rounded whitespace-nowrap pointer-events-none`}>{isInner ? '紅線 (圖案)' : '藍線 (卡邊)'}</div>}
        </div>
    );
  };
  
  const [coordsKey, setCoordsKey] = useState(0);
  useEffect(() => { setTimeout(() => setCoordsKey(k => k + 1), 50); }, [step]); 
  const handleBackToCrop = () => { setStep('crop'); setSelectedLineId(null); setProcessedImage(null); };
  
  const isImageStep = step === 'crop' || step === 'measure';
  const mainClass = `flex-1 relative w-full overflow-auto select-none p-2 md:p-6 flex justify-center ${isImageStep ? 'items-start' : 'items-center'}`; 

  return (
    <div className="h-screen bg-gray-950 text-white font-sans flex flex-col overflow-hidden">
      <header className="bg-gray-900 border-b border-gray-800 h-12 flex items-center justify-between px-4 shrink-0 z-50">
        <div className="flex items-center gap-2"><Ruler className="text-blue-400" size={18} /><span className="font-bold text-sm md:text-base bg-gradient-to-r from-blue-400 to-purple-400 bg-clip-text text-transparent">PTCG Grade (虛線修復版 v22)</span></div>
        <div className="flex items-center gap-2 text-xs">{step !== 'upload' && (<button onClick={() => window.location.reload()} className="hover:text-white text-gray-400 flex items-center gap-1"><RefreshCw size={12}/> 重置</button>)}</div>
      </header>
      <main className={mainClass}>
        {step === 'upload' && (
             <div className="flex-1 flex flex-col items-center justify-center p-6"><div className="w-full max-w-md aspect-[3/4] border-2 border-dashed border-gray-700 rounded-2xl bg-gray-900 hover:border-blue-500 transition-all relative flex flex-col items-center justify-center group cursor-pointer"><Upload size={48} className="text-gray-600 group-hover:text-blue-400 mb-4 transition-colors"/><input type="file" accept="image/*" onChange={handleImageUpload} className="absolute inset-0 opacity-0 cursor-pointer z-10" /><p className="text-gray-400 font-medium">點擊上傳卡牌照片</p><p className="text-gray-600 text-xs mt-2">請確保卡牌四角清晰</p></div></div>
        )}
        {(step === 'crop' || step === 'measure') && (
            <div className={`flex-shrink-0 select-none ${step === 'measure' ? 'max-h-[85vh] overflow-y-auto bg-gray-800 rounded-xl p-2 w-fit max-w-full' : 'relative w-fit h-fit'}`} ref={containerRef}>
                <div className="relative w-fit h-fit">
                    <img ref={imgRef} src={step === 'crop' ? originalImage?.src : processedImage?.src} alt="Work" className="object-contain pointer-events-none shadow-2xl" style={step === 'crop' ? { maxWidth: `${BASE_TARGET_WIDTH}px`, maxHeight: '80vh' } : (processedImage ? { width: `${processedImage.naturalWidth}px`, height: 'auto' } : {})} />
                    
                    {/* 改良後的放大鏡面板: 可收折 */}
                    {(step === 'crop' || step === 'measure') && (
                        <div className={`fixed right-2 top-1/2 transform -translate-y-1/2 bg-gray-800/90 backdrop-blur-sm rounded-lg shadow-xl z-50 flex flex-col gap-2 border border-gray-700 transition-all duration-300 ${isMagnifierPanelCollapsed ? 'p-2 w-10' : 'p-3'}`}>
                             <button 
                                onClick={() => setIsMagnifierPanelCollapsed(!isMagnifierPanelCollapsed)}
                                className="self-end text-gray-400 hover:text-white mb-1 focus:outline-none"
                                title={isMagnifierPanelCollapsed ? "展開" : "收起"}
                            >
                                {isMagnifierPanelCollapsed ? <ChevronLeft size={16}/> : <ChevronRight size={16}/>}
                            </button>
                            
                            {!isMagnifierPanelCollapsed && (
                                <>
                                    <p className="text-xs text-gray-300 font-semibold mb-1 text-center whitespace-nowrap">放大鏡</p>
                                    {zoomOptions.map(z => (<button key={z} onClick={() => handleZoomChange(z)} className={`w-10 h-10 text-xs font-bold rounded-lg transition-all border ${zoomLevel === z ? 'bg-blue-600 text-white shadow-md border-blue-400' : 'bg-gray-700 text-gray-300 hover:bg-gray-600 border-gray-600'}`}>{z.toFixed(1)}X</button>))}
                                    <p className="text-xs text-gray-500 text-center mt-1">1.0X 原圖</p>
                                </>
                            )}
                            {isMagnifierPanelCollapsed && (
                                <div className="flex flex-col items-center gap-1">
                                    <div className="text-[10px] font-bold text-blue-400">{zoomLevel.toFixed(1)}X</div>
                                </div>
                            )}
                        </div>
                    )}
                    
                    {step === 'crop' && originalImage && (
                        <CropOverlay 
                            cropPoints={cropPoints} 
                            getImageContainerRect={getLiveImageRect} 
                            getScreenCoords={getScreenCoords} 
                            activePointIndex={activePointIndex} 
                            handleCropDragStart={handleCropDragStart} 
                            imgRef={imgRef} 
                            key={`crop-overlay-${coordsKey}`} 
                        />
                    )}
                    {step === 'measure' && processedImage && (
                        <div className="absolute inset-0 w-full h-full pointer-events-auto"> 
                            {renderDraggableLine('outerTop', 'horizontal', 'border-blue-500', false)}
                            {renderDraggableLine('outerBottom', 'horizontal', 'border-blue-500', false)}
                            {renderDraggableLine('outerLeft', 'vertical', 'border-blue-500', false)}
                            {renderDraggableLine('outerRight', 'vertical', 'border-blue-500', false)}
                            {renderDraggableLine('innerTop', 'horizontal', 'border-red-500', true)}
                            {renderDraggableLine('innerBottom', 'horizontal', 'border-red-500', true)}
                            {renderDraggableLine('innerLeft', 'vertical', 'border-red-500', true)}
                            {renderDraggableLine('innerRight', 'vertical', 'border-red-500', true)}
                        </div>
                    )}
                </div>
                {isProcessing && (<div className="fixed inset-0 bg-black/80 z-50 flex flex-col items-center justify-center text-white"><Loader2 className="animate-spin mb-4" size={40}/><p>正在進行透視校正 (Homography)...</p></div>)}
            </div>
        )}
      </main>
      <Magnifier magnifierState={{...magnifier, cropPoints: cropPoints, measureLines: measureLines, currentStep: step}} zoom={zoomLevel} cardImage={cardImageForMagnifier}/>
      <footer className="bg-gray-900 border-t border-gray-800 p-3 shrink-0 z-40">
        <div className="max-w-4xl mx-auto w-full">
            {step === 'crop' && (
                <div className="flex flex-col md:flex-row items-center justify-between gap-3">
                     <div className="flex flex-wrap items-center gap-3"><div className="text-gray-400 text-xs md:text-sm"><span className="text-green-400 font-bold">步驟 1:</span> 拖曳四個綠點至卡牌角落</div></div>
                     <button onClick={performWarpAndProceed} className="bg-green-600 hover:bg-green-500 text-white px-6 py-2 rounded-full font-bold shadow-lg flex items-center gap-2 active:scale-95 transition-all w-full md:w-auto justify-center">校正並繼續 <ArrowRight size={18}/></button>
                </div>
            )}
            {step === 'measure' && (
                <div className="flex flex-col gap-3">
                    <div className="flex items-center justify-between"><button onClick={handleBackToCrop} className="text-gray-500 hover:text-white px-2 py-1 flex items-center gap-1 text-xs"><ArrowLeft size={14}/> 重調四角 (保留上次位置)</button><div className="flex items-center gap-2"><button onClick={() => nudgeLine(-1)} disabled={!selectedLineId} className={`w-10 h-10 rounded-full flex items-center justify-center border transition-colors ${selectedLineId ? 'bg-gray-800 hover:bg-gray-700 border-gray-700 text-white' : 'bg-gray-900 border-gray-800 text-gray-600 cursor-not-allowed'}`}>{(selectedLineId?.includes('Top') || selectedLineId?.includes('Bottom')) ? <ChevronUp size={20}/> : <ChevronLeft size={20}/>}</button><div className="text-center w-24"><div className="text-[10px] text-gray-500 uppercase tracking-wider">微調</div><div className="text-xs font-bold text-blue-300 truncate">{selectedLineId ? (selectedLineId.includes('outer') ? '藍線 (卡邊)' : '紅線 (圖案)') : '請點選虛線'}</div></div><button onClick={() => nudgeLine(1)} disabled={!selectedLineId} className={`w-10 h-10 rounded-full flex items-center justify-center border transition-colors ${selectedLineId ? 'bg-gray-800 hover:bg-gray-700 border-gray-700 text-white' : 'bg-gray-900 border-gray-800 text-gray-600 cursor-not-allowed'}`}>{(selectedLineId?.includes('Top') || selectedLineId?.includes('Bottom')) ? <ChevronDown size={20}/> : <ChevronRight size={20}/>}</button></div><div className="w-16"></div></div>
                    <div className="bg-black/40 rounded-lg p-2 flex items-center justify-around border border-gray-700"><div className="flex flex-col items-center w-1/2 border-r border-gray-700"><span className="text-[10px] text-gray-400 uppercase">左右比例 (H)</span><div className="flex items-baseline gap-1"><span className={`text-lg font-bold ${Math.abs(results.h.left - results.h.right) <= 10 ? 'text-green-400' : 'text-yellow-400'}`}>{results.h.left.toFixed(1)} : {results.h.right.toFixed(1)}</span></div></div><div className="flex flex-col items-center w-1/2"><span className="text-[10px] text-gray-400 uppercase">上下比例 (V)</span><div className="flex items-baseline gap-1"><span className={`text-lg font-bold ${Math.abs(results.v.top - results.v.bottom) <= 10 ? 'text-green-400' : 'text-yellow-400'}`}>{results.v.top.toFixed(1)} : {results.v.bottom.toFixed(1)}</span></div></div></div>
                </div>
            )}
        </div>
      </footer>
    </div>
  );
}

const CropOverlay = ({ cropPoints, renderedImageRect, getScreenCoords, activePointIndex, handleCropDragStart, imgRef, getImageContainerRect }) => {
    // 確保這裡使用正確的 rect 獲取方式
    const containerRect = getImageContainerRect ? getImageContainerRect() : (imgRef.current?.getBoundingClientRect() || renderedImageRect);
    
    if (!containerRect || containerRect.width === 0) return null;
    
    const screenPoints = cropPoints.map(p => { 
        const c = getScreenCoords(p.x, p.y); 
        return { c, p, originalIndex: cropPoints.indexOf(p) }; 
    });
    
    if (screenPoints.length !== 4) return null; 
    
    const polygonPoints = screenPoints.map(item => `${item.c.x - containerRect.left},${item.c.y - containerRect.top}`).join(' ');

    return (
        <>
            <svg className="absolute inset-0 w-full h-full pointer-events-none">
                <polygon points={polygonPoints} fill="rgba(34, 197, 94, 0.1)" stroke="rgba(34, 197, 94, 0.8)" strokeWidth="2" strokeDasharray="5" />
            </svg>
            {screenPoints.map((item, i) => (
                <div key={item.originalIndex} className={`fixed w-8 h-8 -ml-4 -mt-4 rounded-full border-2 cursor-move flex items-center justify-center shadow-[0_0_10px_rgba(0,0,0,0.5)] pointer-events-auto transition-transform ${activePointIndex === item.originalIndex ? 'bg-green-400 border-white scale-125 z-30' : 'bg-green-500/80 border-green-200 z-20'}`} style={{ left: item.c.x, top: item.c.y }} onMouseDown={(e) => handleCropDragStart(item.originalIndex, e)} onTouchStart={(e) => handleCropDragStart(item.originalIndex, e)}><Move size={14} className="text-black" /></div>
            ))}
        </>
    );
};

export default function App() {
    return (
        <CardGraderTool />
    )
}
